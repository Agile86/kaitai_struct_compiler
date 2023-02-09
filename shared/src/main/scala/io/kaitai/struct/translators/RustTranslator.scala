package io.kaitai.struct.translators

import io.kaitai.struct.format._
import io.kaitai.struct.datatype._
import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.exprlang.Ast.expr
import io.kaitai.struct.format.{Identifier, IoIdentifier}
import io.kaitai.struct.languages.RustCompiler
import io.kaitai.struct.translators.RustTranslator.makeKey
import io.kaitai.struct.{ClassTypeProvider, RuntimeConfig, Utils}

import scala.collection.mutable
import scala.util.control.Breaks.{break, breakable}

class RustTranslator(provider: TypeProvider, config: RuntimeConfig)
  extends BaseTranslator(provider) {

  import RustCompiler._

  private val reNestedType ="(?:[^<]*<)*([^>]*)>*".r

  def scanClass(cls: ClassSpec): Unit = {
    val clsNames = {
      if (cls.isTopLevel) {
        for ((_, clsType) <- cls.types) {
          for (el <- clsType.seq) {
            if (el.dataType.isInstanceOf[SwitchType])
              RustCompiler.renameEnumAttr = true
          }
        }
        if (cls.seq.nonEmpty) {
          cls.seq.head.dataType match {
            case ut: UserType =>
              List(ut.classSpec.get.name.head)
            case _ =>
              Nil
          }
        } else {
          Nil
        }
      } else {
        cls.name
      }
    }
    val clsName = RustCompiler.types2class(clsNames)

    for ((_, clsType) <- cls.types) {
      scanClass(clsType)
    }

    for (el <- cls.seq) {
      val (resType, _) = RustCompiler.attrProto(el.id, cls, el.dataTypeComposite)
      RustTranslator.addMember(clsName, RustCompiler.enumAttrName(el.id, cls), resType)

      el.dataType match {
        case st: SwitchType =>
          breakable {
            for (kv <- st.cases) {
              val label = kv._1 match {
                case ebl: Ast.expr.EnumByLabel => ebl.label.name
                case in: Ast.expr.IntNum => in.n.toString
                case lst: Ast.expr.List => lst.elts.mkString
                case str: Ast.expr.Str => str.s
                case _ => break
              }
              val caseCls = kv._2 match {
                case ut: UserType => ut.classSpec.get
                case _ => break
              }
              val caseTypeOpt = cls.types.get(label)
              val caseType = if (caseTypeOpt.isDefined) caseTypeOpt.get else caseCls
              val caseAs = caseType.seq.head
              val caseId = caseAs.id
              val caseName = idToStr(caseId)
              val reNestedType(resClsName) = resType
              val (caseResType, _) = RustCompiler.attrProto(caseId, caseCls, caseAs.dataTypeComposite)
              val enumName = RustCompiler.enumAttrName(caseId, caseCls)
              RustTranslator.renamedAttrs(RustTranslator.makeKey(resClsName, caseName)) = enumName
              RustTranslator.addMember(resClsName, caseName, caseResType)
              RustTranslator.addMember(resClsName, enumName, caseResType)
              if (clsNames.nonEmpty)
                RustTranslator.addMember(RustCompiler.types2class(clsNames ::: List(label)), caseName, caseResType)
            }
          }
        case _ =>
      }
    }

    for (el <- cls.params) {
      val typeName = RustCompiler.kaitaiTypeToNativeType(Some(el.id), cls, el.dataType)
      RustTranslator.addMember(clsName, idToStr(el.id), typeName)
    }

    for ((instId, instSpec) <- cls.instances) {
      val typeName = RustCompiler.kaitaiTypeToNativeType(Some(instId), cls, instSpec.dataType)
      RustTranslator.addMember(clsName, idToStr(instId), typeName)
    }

    if (cls.isTopLevel) {
      RustCompiler.renameEnumAttr = false
      for((was, ren) <- RustTranslator.renamedAttrs) {
        RustTranslator.log(s"$was -> $ren\n")
      }
    }
  }

  for(cls <- provider.asInstanceOf[ClassTypeProvider].allClasses) {
    scanClass(cls._2)
  }

  override def doByteArrayLiteral(arr: Seq[Byte]): String =
    "vec![" + arr.map(x => "%0#2xu8".format(x & 0xff)).mkString(", ") + "]"
  override def doByteArrayNonLiteral(elts: Seq[Ast.expr]): String =
    "vec![" + elts.map(translate).mkString(", ") + "]"
  override def doArrayLiteral(t: DataType, value: Seq[Ast.expr]): String = {
    t match {
      case CalcStrType => "vec![" + value.map(v => translate(v)).mkString(".to_string(), ") + ".to_string()]"
      case _ => "vec![" + value.map(v => translate(v)).mkString(", ") + "]"
    }
  }

  override val asciiCharQuoteMap: Map[Char, String] = Map(
    '\t' -> "\\t",
    '\n' -> "\\n",
    '\r' -> "\\r",
    '"' -> "\\\"",
    '\\' -> "\\\\"
  )

  override def strLiteralGenericCC(code: Char): String =
    strLiteralUnicode(code)

  override def strLiteralUnicode(code: Char): String =
    "\\u{%x}".format(code.toInt)

  def isSignedIntType(dt: DataType): Boolean = dt match {
    case Int1Type(true) => true
    case IntMultiType(true, _, _) => true
    case CalcIntType => true
    case _ => false
  }

  def isAllDigits(x: String): Boolean = x forall Character.isDigit

  override def numericBinOp(left: Ast.expr,
                            op: Ast.operator,
                            right: Ast.expr): String = {
    val lt = detectType(left)
    val rt = detectType(right)
    val tl = translate(left)
    val tr = translate(right)

    if (isSignedIntType(lt) && isSignedIntType(rt) && op == Ast.operator.Mod) {
        s"modulo($tl as i64, $tr as i64)"
    } else if (isSignedIntType(lt) && isSignedIntType(rt) && op == Ast.operator.RShift) {
        // Arithmetic right shift on signed integer types, logical right shift on unsigned integer types
        val ct = RustCompiler.kaitaiPrimitiveToNativeType(TypeDetector.combineTypes(lt, rt))
        s"((($tl as u64) >> $tr) as $ct)"
    } else {
      if (lt == rt && isAllDigits(tl) && isAllDigits(tr)) {
        // let rust decide final type
        s"($tl ${binOp(op)} $tr)"
      } else {
        val ct = RustCompiler.kaitaiPrimitiveToNativeType(TypeDetector.combineTypes(lt, rt))
        s"(($tl as $ct) ${binOp(op)} ($tr as $ct))"
      }
    }
  }

  private var lastResult: String = ""
  private var callTranslateDepth: Int = 0
  private val reRefOpt = "^Ref<Option<.*".r

  def unwrap(s: String): String = s + ".as_ref().unwrap()"

  override def doName(s: String): String = s match {
    case Identifier.PARENT => s
    case _ =>
      val memberFound = findMember(s)
      if (memberFound.isDefined) {
        val spec = memberFound.get

        spec match {
          case _: ParseInstanceSpec =>
            s"$s(${privateMemberName(IoIdentifier)})?"
          case vis: ValueInstanceSpec =>
            val aType = RustCompiler.kaitaiTypeToNativeType(Some(vis.id), provider.nowClass, vis.dataTypeComposite)
            if (reRefOpt.findFirstIn(aType).isDefined)
              unwrap(s"$s()")
            else
              s"$s()?"

          case as: AttrSpec =>
            val cls = if (RustCompiler.nowClass != null) RustCompiler.nowClass else provider.nowClass
            var aType = types2class(cls.name)
            var newName = RustTranslator.renamedAttrs.get(makeKey(aType, s))
            if (newName.isEmpty) {
              aType = lastResult
              newName = RustTranslator.renamedAttrs.get(makeKey(aType, s))
            }
            if (newName.isEmpty) {
              for(tp <- RustTranslator.getTypes(s); if newName.isEmpty) {
                aType = tp
                newName = RustTranslator.renamedAttrs.get(makeKey(aType, s))
              }
            }
            val code = if (newName.isDefined) s"${newName.get}()" else s"$s()"
            var proto = RustTranslator.getProto(aType, s).getOrElse("")
            val reNestedType(nestedType) = if(proto.nonEmpty) {
              proto
            } else {
              val types = RustTranslator.getTypes(s)
              if (types.size == 1) types.head else "<>"
            }
            if (nestedType.nonEmpty) {
              lastResult = nestedType
              if (proto.isEmpty)
                proto = RustTranslator.getProto(nestedType, s).getOrElse("")
            }

            if (reRefOpt.findFirstIn(proto).isDefined && !enum_numeric_only(as.dataTypeComposite))
              unwrap(code)
            else
              code

            /*
            case pd: ParamDefSpec =>
              val aType = RustCompiler.kaitaiTypeToNativeType(Some(pd.id), provider.nowClass, pd.dataTypeComposite)
              val refOpt = "^Option<.*".r
              aType match {
                case refOpt() => s"$s().as_ref().unwrap()"
                case _ => s"$s()"
              }
            case pis: ParseInstanceSpec =>
              //s"$s(${privateMemberName(IoIdentifier)})?"
              val aType = RustCompiler.kaitaiTypeToNativeType(Some(pis.id), provider.nowClass, pis.dataTypeComposite)
              val refOpt = "^Option<.*".r
              aType match {
                case refOpt() => s"$s(${privateMemberName(IoIdentifier)})?.as_ref().unwrap()"
                case _ => s"$s(${privateMemberName(IoIdentifier)})?"
              }

             */
          case pd: ParamDefSpec =>
            pd.dataType match {
              case _: NumericType | _: BooleanType | _: EnumType | _: ArrayType => s"$s()"
              case _: CalcUserType =>
                val code = s"$s()"
                val aType = RustCompiler.kaitaiTypeToNativeType(Some(pd.id), provider.nowClass, pd.dataTypeComposite)
                if (!aType.startsWith("Rc<"))
                  unwrap(s"$code")
                else
                  code
              case _ =>
                unwrap(s"$s()")
            }
          case _ =>
            s"$s()"
        }
      } else {
        s"$s()"
      }
  }

  def findMember(attrName: String, c: ClassSpec = provider.nowClass): Option[MemberSpec] = {
    def findInClass(inClass: ClassSpec): Option[MemberSpec] = {

      inClass.seq.foreach { el =>
        if (idToStr(el.id) == attrName) {
          return Some(el)
        }
      }

      inClass.params.foreach { el =>
        if (idToStr(el.id) == attrName) {
          return Some(el)
        }
      }

      inClass.instances.foreach { case (instName, instSpec) =>
        if (idToStr(instName) == attrName) {
          return Some(instSpec)
        }
      }

      inClass.types.foreach { t =>
        for {found <- findInClass(t._2)}
          return Some(found)
      }
      None
    }

    val attr = attrName match {
      case Identifier.PARENT | Identifier.IO =>
        None
      case _ =>
        for {ms <- findInClass(get_top_class(c))}
          return Some(ms)

        provider.asInstanceOf[ClassTypeProvider].allClasses.foreach { cls =>
          for {ms <- findInClass(cls._2)}
            return Some(ms)
        }
        None
    }
    attr
  }

  def get_top_class(c: ClassSpec): ClassSpec = c.upClass match {
    case Some(upClass) => get_top_class(upClass)
    case None => c
  }

  def get_instance(cs: ClassSpec, s: String): Option[InstanceSpec] = {
    var found : Option[InstanceSpec] = None
    // look for instance
    cs.instances.foreach { case (instName, instSpec) =>
      if (idToStr(instName) == s) {
        found = Some(instSpec)
      }
    }
    // look deeper
    if (found.isEmpty) {
      cs.types.foreach {
        case (_, typeSpec) =>
          found = get_instance(typeSpec, s)
          if (found.isDefined) {
            return found
          }
        }
    }
    found
  }

  override def anyField(value: expr, attrName: String): String = {
    def addSuffix(doAdd: Boolean, suffix: String): String = {
      if (doAdd) suffix else ""
    }
    def needUnwrap(): Boolean = {
      value match {
        case name: Ast.expr.Name =>
          name.id.name == Identifier.ROOT
        case ctt: Ast.expr.CastToType =>
          ctt.value match {
            case attr: Ast.expr.Attribute =>
              attr.attr match {
                case id: Ast.identifier =>
                  val proto = RustTranslator.getProto("", id.name)
                  if (proto.isDefined)
                    return reRefOpt.findFirstIn(proto.get).isDefined
                  else {
                    false
                  }
                case _ =>
                  false
              }
            case _ =>
              false
          }
        case _ =>
          false
      }
      false
    }

    val t = translate(value) + addSuffix(needUnwrap(), unwrap(""))
    val valType = detectType(value)
    valType match {
      case ut: UserType =>
        if (ut.classSpec.isDefined) {
          RustCompiler.nowClass = ut.classSpec.get
        }
      case _ =>
    }
    val a = doName(attrName) + addSuffix(attrName == Identifier.PARENT, unwrap(".get_value().borrow()"))
    var r = ""

    if (need_deref(attrName)) {
      if (t.charAt(0) == '*') {
        r = s"$t.$a"
      } else {
        r = s"*$t.$a"
      }
    } else {
      if (t.charAt(0) == '*') {
        r = s"${t.substring(1)}.$a"
      } else {
        r = s"$t.$a"
      }
    }
    r
  }

  def rem_vec_amp(s: String): String = {
    if (s.startsWith("&vec!")) {
      s.substring(1)
    } else {
      s
    }
  }

  def ensure_vec_amp(s: String): String = {
    if (s.startsWith("vec!")) {
      s"&$s"
    } else {
      s
    }
  }

  def ensure_amp(s: String): String = {
    if (s.charAt(0) == '&') {
      s
    } else {
      s"&$s"
    }
  }

  def remove_deref(s: String): String = {
    if (s.charAt(0) == '*') {
      s.substring(1)
    } else {
      s
    }
  }

  def ensure_deref(s: String): String = {
    if (s.startsWith(self_name())) {
      s"*$s"
    } else {
      s
    }
  }

  def enum_numeric_only(dataType: DataType): Boolean = {
    var types : Set[DataType] = Set()
    var enum_typename = false
    dataType match {
      case st: SwitchType =>
        types = st.cases.values.toSet
        enum_typename = true
      //case _: EnumType => return true
      case _ => return false
    }
    var enum_only_numeric = true
    types.foreach {
      case _: NumericType => // leave unchanged
      case _ => enum_only_numeric = false
    }
    enum_only_numeric
  }

  def is_copy_type(dataType: DataType): Boolean = dataType match {
    case _: SwitchType => false
    case _: UserType => false
    case _: BytesType => false
    case _: ArrayType => false
    case _: StrType => false
    case _: EnumType => false
    case _ => true
  }

  def need_deref(s: String, c: ClassSpec = provider.nowClass): Boolean = {
    var deref = false
    val memberFound = findMember(s, c)
    if (memberFound.isDefined ) {
      val spec = memberFound.get
      spec match {
        case _: AttrSpec | _: ParamDefSpec  =>
          deref = !enum_numeric_only(spec.dataTypeComposite)
        case _: ValueInstanceSpec | _: ParseInstanceSpec | _: ParamDefSpec =>
          deref = true
        case _ =>
      }
    } else {
      for (kv <- RustTranslator.renamedAttrs) {
        if (kv._2 == s) {
          val (k, m) = RustTranslator.splitKey(kv._1)
          val proto = RustTranslator.getProto(k, m)
          deref = proto.isDefined && proto.get.startsWith("Ref<")
        }
      }
    }

    deref
  }

  override def doLocalName(s: String): String = s match {
    case Identifier.ITERATOR => "_tmpa"
    case Identifier.ITERATOR2 => "_tmpb"
    case Identifier.INDEX => "_i"
    case Identifier.IO => s"${RustCompiler.privateMemberName(IoIdentifier)}"
    case Identifier.ROOT => s"_r"
    case Identifier.PARENT => s"_prc.as_ref().unwrap()"
    case _ =>
      val n = doName(s)
      val deref = !n.endsWith(".as_str()") && !n.endsWith(".as_slice()") && need_deref(s)
      if (deref) {
        s"*${self_name()}.$n"
      } else {
        s"${self_name()}.$n"
      }
  }
  override def doEnumCompareOp(left: Ast.expr, op: Ast.cmpop, right: Ast.expr): String = {
    val code = s"${translate(left)} ${cmpOp(op)} ${translate(right)}"
    code
  }

  override def doInternalName(id: Identifier): String =
    s"${doLocalName(idToStr(id))}"

  override def doEnumByLabel(enumTypeAbs: List[String], label: String): String =
    s"${RustCompiler.types2class(enumTypeAbs)}::${Utils.upperCamelCase(label)}"

  override def doNumericCompareOp(left: Ast.expr, op: Ast.cmpop, right: Ast.expr): String = {
    val lt = detectType(left)
    val rt = detectType(right)
    if (lt != rt) {
      val ct = RustCompiler.kaitaiPrimitiveToNativeType(TypeDetector.combineTypes(lt, rt))
      s"((${translate(left)} as $ct) ${cmpOp(op)} (${translate(right)} as $ct))"
    } else {
      s"${translate(left)} ${cmpOp(op)} ${translate(right)}"
    }
  }

  override def doStrCompareOp(left: Ast.expr, op: Ast.cmpop, right: Ast.expr): String = {
    s"${ensure_deref(translate(left))} ${cmpOp(op)} ${remove_deref(translate(right))}.to_string()"
  }

  override def doEnumById(enumTypeAbs: List[String], id: String): String =
    s"($id as i64).try_into()?"

  override def arraySubscript(container: expr, idx: expr): String =
    s"${remove_deref(translate(container))}[${translate(idx)} as usize]"

  override def doIfExp(condition: expr, ifTrue: expr, ifFalse: expr): String = {
    var to_type = ""
    detectType(ifTrue) match {
      case _: UserType => to_type = ".clone()"
      case _: EnumType => to_type = ".clone()"
      case _: StrType => to_type = ".to_string()"
      case _: BytesType => to_type = ".to_vec()"
      case _: CalcArrayType => to_type = ".clone()"
      case _ =>
    }
    if (to_type.isEmpty) {
      s"if ${translate(condition)} { ${translate(ifTrue)} } else { ${translate(ifFalse)} }"
    } else {
      s"if ${translate(condition)} { ${remove_deref(translate(ifTrue))}$to_type } else { ${remove_deref(translate(ifFalse))}$to_type }"
    }
  }

  override def doCast(value: Ast.expr, castTypeName: DataType): String = {
    val value_type = detectType(value)
    if(castTypeName == value_type)
      return translate(value)

    val ct = RustCompiler.kaitaiTypeToNativeType(None, provider.nowClass, castTypeName, excludeOptionWrapper = true)
    var into = false
    castTypeName match {
      case _: UserType => into = true;
      case CalcBytesType => into = true;
      case _ =>
    }
    if (into) {
      s"Into::<$ct>::into(&${translate(value)})"
    } else {
      s"(${translate(value)} as $ct)"
    }
  }

  override def translate(v: Ast.expr): String = {
    callTranslateDepth += 1
    val result = v match {
      case Ast.expr.EnumById(enumType, id, inType) =>
        id match {
          case ifExp: Ast.expr.IfExp =>
            val enumSpec = provider.resolveEnum(inType, enumType.name)
            val enumName = RustCompiler.types2class(enumSpec.name)
            def toStr(ex: Ast.expr) = ex match {
              case Ast.expr.IntNum(n) => s"$enumName::try_from($n)?"
              case _ => super.translate(ex)
            }
            val ifTrue = toStr(ifExp.ifTrue)
            val ifFalse = toStr(ifExp.ifFalse)

            "if " + translate(ifExp.condition) + s" { $ifTrue } else { $ifFalse }"
          case _ => super.translate(v)
        }
      case _ =>
        super.translate(v)
    }
    callTranslateDepth -= 1
    if(callTranslateDepth == 0)
      lastResult = ""

    result
  }

  // Predefined methods of various types
  override def strConcat(left: Ast.expr, right: Ast.expr): String =
    s"""format!("{}{}", ${translate(left)}, ${translate(right)})"""

  override def strToInt(s: expr, base: expr): String =
    translate(base) match {
      case "10" =>
        s"${translate(s)}.parse::<i32>().unwrap()"
      case _ =>
        s"i32::from_str_radix(${translate(s)}, ${translate(base)}).unwrap()"
    }

  override def enumToInt(v: expr, et: EnumType): String =
    s"i64::from(&${translate(v)})"

  override def boolToInt(v: expr): String =
    s"(${translate(v)}) as i32"

  override def floatToInt(v: expr): String =
    s"${translate(v)} as i32"

  override def intToStr(i: expr, base: expr): String = {
    val baseStr = translate(base)
    baseStr match {
      case "10" =>
         s"${remove_deref(translate(i))}.to_string()"
      case _ =>
        s"base_convert(strval(${translate(i)}), 10, $baseStr)"
    }
  }
  override def bytesToStr(bytesExpr: String, encoding: Ast.expr): String = {
    if (bytesExpr.charAt(0) == '*') {
      s"decode_string(&$bytesExpr, &${translate(encoding)})?"
    } else {
      s"decode_string(${ensure_vec_amp(bytesExpr)}, &${translate(encoding)})?"
    }
  }

  override def bytesLength(b: Ast.expr): String =
    s"${remove_deref(translate(b))}.len()"
  override def strLength(s: expr): String =
    s"${remove_deref(translate(s))}.len()"
  override def strReverse(s: expr): String = {
    val e = translate(s)
    if (e.charAt(0) == '*')
      s"reverse_string(&$e)?"
    else
      s"reverse_string($e)?"
  }
  override def strSubstring(s: expr, from: expr, to: expr): String =
    s"${translate(s)}[${translate(from)}..${translate(to)}]"

  override def arrayFirst(a: expr): String =
    s"${ensure_deref(translate(a))}.first().ok_or(KError::EmptyIterator)?"
  override def arrayLast(a: expr): String =
    s"${ensure_deref(translate(a))}.last().ok_or(KError::EmptyIterator)?"
  override def arraySize(a: expr): String =
    s"${remove_deref(translate(a))}.len()"

  def is_float_type(a: Ast.expr): Boolean = {
    detectType(a) match {
      case t: CalcArrayType =>
        t.elType match {
          case _: FloatMultiType => true
          case CalcFloatType => true
          case _ => false
        }
      case t: ArrayType =>
        t.elType match  {
          case _: FloatMultiType => true
          case _ => false
        }
      case _ => false
    }
  }

  override def arrayMin(a: Ast.expr): String = {
    if (is_float_type(a)) {
      s"${ensure_deref(translate(a))}.iter().reduce(|a, b| if (a.min(*b)) == *b {b} else {a}).ok_or(KError::EmptyIterator)?"
    } else {
      s"${ensure_deref(translate(a))}.iter().min().ok_or(KError::EmptyIterator)?"
    }
  }

  override def arrayMax(a: Ast.expr): String = {
    if (is_float_type(a)) {
      s"${ensure_deref(translate(a))}.iter().reduce(|a, b| if (a.max(*b)) == *b {b} else {a}).ok_or(KError::EmptyIterator)?"
    } else {
      s"${ensure_deref(translate(a))}.iter().max().ok_or(KError::EmptyIterator)?"
    }
  }
}

object RustTranslator {
  private class ConsoleRedirect extends java.io.Writer {
    override def write(cbuf: Array[Char], off: Int, len: Int): Unit =
      print(cbuf.slice(off, len).mkString)
    override def flush(): Unit = ()
    override def close(): Unit = ()
  }

  private class PrinterAutoflush(file: java.io.File) extends java.io.PrintWriter(file) {
    override def write(s: String): Unit = {
      super.write(s)
      flush()
    }
  }

  lazy val logWriter: java.io.Writer = {
    val envLog = sys.env.get("LOG_RUST")
    if (envLog.isDefined) {
      envLog.get match {
        case "" => null
        case "CONSOLE" => new ConsoleRedirect()
        case fileName => new PrinterAutoflush(new java.io.File(fileName) )
      }
    } else {
      null
    }
  }
  def log(msg: String): Unit = if (logWriter != null) logWriter.write(msg)

  def makeKey(memType: String, memName: String): String
    = memType + ":" + memName

  def splitKey(key: String): (String, String) =
    if (key.contains(":")) {
      val parts = key.split(":")
      (parts(0), parts(1))
    } else {
      ("", "")
    }

  def addMember(memType: String, memName: String, proto: String): Unit = {
    val key = makeKey(memType, memName)
    log(s"addMember: $key -> $proto\n")
    prototypes(key) = proto
  }

  def getProto(memType: String, memName: String): Option[String] = {
    val k = makeKey(memType, memName)
    val key = if (renamedAttrs.contains(k)) makeKey(memType, renamedAttrs(k)) else k
    log(s"proto: $key")
    val proto = prototypes.get(key)
    log(s" -> $proto\n")
    proto
  }

  def getTypes(memName: String): List[String] = {
    val types = for {
      item <- prototypes
      parts = splitKey(item._1)
      if memName == parts._2
    } yield parts._1

    log(s"types for $memName:\n")
    for(el <- types)
      log(s"  $el\n")

    types.toList
  }

  val prototypes: mutable.Map[String, String] = mutable.Map[String, String]()
  val renamedAttrs: mutable.Map[String, String] = mutable.Map[String, String]()
}
