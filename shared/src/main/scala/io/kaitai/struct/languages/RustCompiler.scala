package io.kaitai.struct.languages

import io.kaitai.struct._
import io.kaitai.struct.datatype.DataType.{ReadableType, _}
import io.kaitai.struct.datatype._
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.format._
import io.kaitai.struct.languages.RustCompiler.TypeKind.TypeKind
import io.kaitai.struct.languages.RustCompiler.idToStr
import io.kaitai.struct.languages.components._
import io.kaitai.struct.translators.RustTranslator
import io.kaitai.struct.{ClassTypeProvider, RuntimeConfig}

import scala.annotation.tailrec

class RustCompiler(typeProvider: ClassTypeProvider, config: RuntimeConfig)
  extends LanguageCompiler(typeProvider, config)
    with AllocateIOLocalVar
    with EveryReadIsExpression
    with FixedContentsUsingArrayByteLiteral
    with ObjectOrientedLanguage
    with SingleOutputFile
    with UpperCamelCaseClasses
    with UniversalFooter
    with SwitchIfOps
    with UniversalDoc {

  import RustCompiler._

  override val translator: RustTranslator =
    new RustTranslator(typeProvider, config)

  override def innerClasses = false

  override def innerEnums = false

  override def indent: String = "    "

  override def outFileName(topClassName: String): String = s"$topClassName.rs"

  override def outImports(topClass: ClassSpec): String =
    importList.toList
      .mkString("", "\n", "\n")

  override def fileHeader(topClassName: String): Unit = {
    outHeader.puts(s"// $headerComment")
    outHeader.puts

    outHeader.puts("#![allow(unused_imports)]")
    outHeader.puts("#![allow(non_snake_case)]")
    outHeader.puts("#![allow(non_camel_case_types)]")
    outHeader.puts("#![allow(irrefutable_let_patterns)]")
    outHeader.puts("#![allow(unused_comparisons)]")
    outHeader.puts
    outHeader.puts("extern crate kaitai;")

    importList.add(
      """use kaitai::*;
        |use kaitai::pt::*;
        |""".stripMargin
    )
    importList.add("use std::convert::{TryFrom, TryInto};")
    importList.add("use std::cell::{Ref, Cell, RefCell};")

    typeProvider.allClasses.foreach{
      case (name, _) =>
        if(name != topClassName) //TODO: do not add to imported
          importList.add(s"use super::$name::*;")
    }
  }

  override def opaqueClassDeclaration(classSpec: ClassSpec): Unit =
    importList.add(
      s"use super::${classSpec.name.last}::${type2class(classSpec.name.last)};"
    )

  override def classHeader(name: List[String]): Unit = {
    val className = classTypeName(typeProvider.nowClass)
    out.puts
    out.puts("#[derive(Default, Debug, PartialEq, Clone)]")
    out.puts(s"pub struct $className {")
    out.inc

    // Because we can't predict whether opaque types will need lifetimes as a type parameter,
    // everyone gets a phantom data marker
    //out.puts(s"_phantom: std::marker::PhantomData<&$streamLife ()>,")

    out.puts(s"${privateMemberName(RootIdentifier)}: ParamType<Box<${types2class(name.slice(0, 1))}>>,")

    typeProvider.nowClass.params.foreach { p =>
      // Make sure the parameter is imported if necessary
      p.dataType match {
        case u: UserType => if (u.isOpaque && u.classSpec.isDefined) opaqueClassDeclaration(u.classSpec.get)
        case _ => ()
      }

      // Declare parameters as if they were attributes
      attributeDeclaration(p.id, p.dataType, isNullable = false)
    }
  }

  // Intentional no-op; Rust has already ended the struct definition by the time we reach this
  override def classFooter(name: List[String]): Unit = {}

  override def classConstructorHeader(name: List[String],
                                      parentType: DataType,
                                      rootClassName: List[String],
                                      isHybrid: Boolean,
                                      params: List[ParamDefSpec]): Unit = {
    typeProvider.nowClass.meta.endian match {
      case Some(_: CalcEndian) | Some(InheritedEndian) =>
        attributeDeclaration(EndianIdentifier, IntMultiType(signed = true, Width4, None), isNullable = false)
      case _ =>
    }

    // Unlike other OOP languages, implementing an interface happens outside the struct declaration.
    universalFooter

    // If there are any switch types in the struct definition, create the enums for them
    typeProvider.nowClass.seq.foreach(
      a =>
        a.dataType match {
          case st: SwitchType => switchTypeEnum(a.id, st)
          case _ => ()
        }
    )
    typeProvider.nowClass.instances.foreach(
      i =>
        i._2.dataTypeComposite match {
          case st: SwitchType => switchTypeEnum(i._1, st)
          case _ => ()
        }
    )

    out.puts(
      s"impl<$readLife, $streamLife: $readLife> $kstructName<$readLife, $streamLife> for ${classTypeName(typeProvider.nowClass)} {"
    )
    out.inc
    out.puts(s"type Root = ${types2class(name.slice(0, 1))};")
    out.puts(
      s"type ParentStack = ${parentStackTypeName(typeProvider.nowClass)};"
    )
    out.puts
  }

  override def runRead(name: List[String]): Unit = {}

  override def runReadCalc(): Unit = {
    out.puts(s"if *${privateMemberName(EndianIdentifier)}.borrow() == 0 {")
    out.inc
    out.puts(s"""return Err(KError::UndecidedEndiannessError("${typeProvider.nowClass.path.mkString("/", "/", "")}".to_string()));""")
    out.dec
    out.puts("}")
  }

  override def readHeader(endian: Option[FixedEndian],
                          isEmpty: Boolean): Unit = {
    out.puts(s"fn read<S: $kstreamName>(")
    out.inc
    out.puts(s"&self,")
    out.puts(s"${privateMemberName(IoIdentifier)}: &$streamLife S,")
    out.puts(
      s"${privateMemberName(RootIdentifier)}: Option<&$readLife Self::Root>,"
    )
    out.puts(
      s"${privateMemberName(ParentIdentifier)}: Option<TypedStack<Self::ParentStack>>,"
    )
    out.dec
    out.puts(s") -> KResult<()> {")
    out.inc

    if (translator.provider.nowClass.name.size == 1) {
      out.puts(
        s"""*self.${privateMemberName(RootIdentifier)}.borrow_mut() = match _root  {
           |            None => Some(Box::new(self.clone())),
           |            Some(p) => Some(Box::new(p.clone())),
           |        };""".stripMargin)
    } else {
      out.puts("*self._root.borrow_mut() = Some(Box::new(_root.unwrap().clone()));")
    }

    // If there aren't any attributes to parse, we need to end the read implementation here
    if (typeProvider.nowClass.seq.isEmpty)
      endRead()
  }

  override def readFooter(): Unit = out.puts(s"// readFooter()")

  override def attributeDeclaration(attrName: Identifier,
                                    attrType: DataType,
                                    isNullable: Boolean): Unit = {
    val nativeType = attrName match {
      // For keeping lifetimes simple, we don't store _io, _root, or _parent with the struct
      case IoIdentifier | RootIdentifier | ParentIdentifier =>
        return
      case EndianIdentifier =>
        kaitaiTypeToNativeTypeWrapper(Some(attrName), attrType).copy(kind = TypeKind.RefCell)
      case _ =>
        kaitaiTypeToNativeTypeWrapper(Some(attrName), attrType)
    }

    out.puts(s"${idToStr(attrName)}: ${nativeType.attrType},")
  }

  def kaitaiTypeToNativeTypeWrapper(id: Option[Identifier],
                                    attrType: DataType): NativeType = {
    if (id.isDefined) id.get match {
      case RawIdentifier(inner) =>
        val found = translator.get_instance(typeProvider.nowClass, idToStr(inner))
        if (found.isDefined) {
          // raw id for instance should have RefCell wrapper
          return kaitaiTypeToNativeType(id, typeProvider.nowClass, attrType).copy(kind = TypeKind.ParamBox)
        }
      case _ =>
    }
    kaitaiTypeToNativeType(id, typeProvider.nowClass, attrType)
  }

  override def attributeReader(attrName: Identifier,
                               attrType: DataType,
                               isNullable: Boolean): Unit = {
    val nativeType = attrName match {
          // For keeping lifetimes simple, we don't store _io, _root, or _parent with the struct
          case IoIdentifier | RootIdentifier | ParentIdentifier => return
          case _ =>
            kaitaiTypeToNativeTypeWrapper(Some(attrName), attrType)
        }
    val className = classTypeName(typeProvider.nowClass)

    out.puts(s"impl<$readLife, $streamLife: $readLife> $className {")
    out.inc

    var types : Set[DataType] = Set()
    var enum_typename = false
    attrType match {
      case st: SwitchType =>
        types = st.cases.values.toSet
        enum_typename = true
      case _: EnumType => // TODO? enum_typename = true
      case _ =>
    }
    var enum_only_numeric = true
    types.foreach {
      case _: NumericType => // leave unchanged
      case _ => enum_only_numeric = false
    }
    var fn = idToStr(attrName)
    if (enum_typename && enum_only_numeric) {
      out.puts(s"pub fn $fn(&self) -> usize {")
      out.inc
      out.puts(s"self.${idToStr(attrName)}.as_ref().unwrap().into()")
      out.dec
      out.puts("}")
      fn = s"${fn}_enum"
    }
    {
      out.puts(nativeType.attrGetterDcl(fn))
      out.inc
      out.puts(nativeType.attrGetterImpl(idToStr(attrName)))
    }
    out.dec
    out.puts("}")
    out.dec
    out.puts("}")
  }

  override def attrParse(attr: AttrLikeSpec,
                         id: Identifier,
                         defEndian: Option[Endianness]): Unit = {
    super.attrParse(attr, id, defEndian)

    // Detect if this is the last attribute parse and finish the read method
    if (typeProvider.nowClass.seq.nonEmpty && typeProvider.nowClass.seq.last.id == id)
      endRead()
  }

  def endRead(): Unit = {
    out.puts("Ok(())")
    out.dec
    out.puts("}")
  }

  override def attrParseHybrid(leProc: () => Unit, beProc: () => Unit): Unit = {}

  override def condIfHeader(expr: Ast.expr): Unit = {
    out.puts(s"if ${expression(expr)} {")
    out.inc
  }

   override def condRepeatCommonInit(id: Identifier, dataType: DataType, needRaw: NeedRaw): Unit = {
    // this line required for handleAssignmentRepeatUntil
    typeProvider._currentIteratorType = Some(dataType)
    out.puts(s"*${privateMemberName(id)}.borrow_mut() = Vec::new();")
  }

  override def condRepeatEosHeader(id: Identifier,
                                   io: String,
                                   dataType: DataType): Unit = {
    out.puts("{")
    out.inc
    out.puts(s"let mut _i = 0;")
    out.puts(s"while !_io.is_eof() {")
    out.inc
  }

  override def handleAssignmentRepeatEos(id: Identifier, expr: String): Unit = {
//    if (in_instance) {
      out.puts(s"${privateMemberName(id)}.borrow_mut().push($expr);")
//    } else {
//      out.puts(s"${privateMemberName(id)}.push($expr);")
//    }
  }

  override def condRepeatEosFooter: Unit = {
    out.puts("_i += 1;")
    out.dec
    out.puts("}")
    out.dec
    out.puts("}")
  }

  override def condRepeatExprHeader(id: Identifier,
                                    io: String,
                                    dataType: DataType,
                                    repeatExpr: Ast.expr): Unit = {
    val lenVar = s"l_${idToStr(id)}"
    out.puts(s"let $lenVar = ${expression(repeatExpr)};")
    out.puts(s"for _i in 0..$lenVar {")
    out.inc
  }

  override def condRepeatUntilHeader(id: Identifier,
                                     io: String,
                                     dataType: DataType,
                                     repeatExpr: Ast.expr): Unit = {
    out.puts("{")
    out.inc
    out.puts("let mut _i = 0;")
    out.puts("while {")
    out.inc
  }

  override def handleAssignmentRepeatUntil(id: Identifier,
                                           expr: String,
                                           isRaw: Boolean): Unit = {
    out.puts(s"${privateMemberName(id)}.push($expr);")
    var copy_type = ""
    if (typeProvider._currentIteratorType.isDefined && RustTranslator.is_copy_type(typeProvider._currentIteratorType.get)) {
      copy_type = "*"
    }
    out.puts(s"let ${translator.doLocalName(Identifier.ITERATOR)} = $copy_type${privateMemberName(id)}.last().unwrap();")
  }

  override def condRepeatUntilFooter(id: Identifier,
                                     io: String,
                                     dataType: DataType,
                                     repeatExpr: Ast.expr): Unit = {
    // this line required by kaitai code
    typeProvider._currentIteratorType = Some(dataType)
    out.puts("_i += 1;")
    out.puts(s"!(${expression(repeatExpr)})")
    out.dec
    out.puts("} {}")
    out.dec
    out.puts("}")
  }

  def getRawIdExpr(varName: Identifier, rep: RepeatSpec): String = {
    val memberName = privateMemberName(varName)
    rep match {
      case NoRepeat => memberName
      case _ => s"$memberName[$memberName.len() - 1]"
    }
  }

  override def attrProcess(proc: ProcessExpr, varSrc: Identifier, varDest: Identifier, rep: RepeatSpec): Unit = {
    val srcExpr = getRawIdExpr(varSrc, rep)

    val expr = proc match {
      case ProcessXor(xorValue) =>
        translator.detectType(xorValue) match {
          case _: IntType =>
            s"S::process_xor_one($srcExpr.borrow().as_slice(), ${expression(xorValue)})"
          case _: BytesType =>
            s"S::process_xor_many($srcExpr.borrow().as_slice(), &${translator.remove_deref(expression(xorValue))})"
          case _ =>
            ???
        }
      case ProcessZlib =>
        s"S::process_zlib(&$srcExpr)"
      case ProcessRotate(isLeft, rotValue) =>
        val expr = if (isLeft) {
          expression(rotValue)
        } else {
          s"8 - (${expression(rotValue)})"
        }
        s"S::process_rotate_left(&$srcExpr, $expr)"
      case ProcessCustom(name, args) =>
        val procClass = name.map(x => type2class(x)).mkString("::")
        val procName = s"_process_${idToStr(varSrc)}"

        val mod_name = name.last
        importList.add(s"""#[path = "$mod_name.rs"] mod $mod_name;""")
        importList.add(s"use self::$mod_name::*;")

        val argList = args.map(expression).mkString(", ")
        val argListInParens = s"($argList)"
        out.puts(s"let $procName = $procClass::new$argListInParens;")
        s"$procName.decode($srcExpr.as_slice())"
    }
    handleAssignment(varDest, expr, rep, isRaw = false)
  }

  override def useIO(ioEx: Ast.expr): String = {
    out.puts(s"let io = BytesReader::new(&${expression(ioEx)});")
    "io"
  }

  override def pushPos(io: String): Unit =
    out.puts(s"let _pos = $io.pos();")

  override def seek(io: String, pos: Ast.expr): Unit =
    out.puts(s"$io.seek(${expression(pos)} as usize)?;")

  override def popPos(io: String): Unit =
    out.puts(s"$io.seek(_pos)?;")

  override def alignToByte(io: String): Unit =
    out.puts(s"${privateMemberName(IoIdentifier)}.align_to_byte()?;")

  override def privateMemberName(id: Identifier): String =
    RustCompiler.privateMemberName(id)

  override def instanceDeclHeader(className: List[String]): Unit = {
    if (typeProvider.nowClass.params.nonEmpty) {
      val paramsArg = Utils.join(typeProvider.nowClass.params.map { p =>
        val n = paramName(p.id)
        val nativeType = kaitaiTypeToNativeType(Some(p.id), typeProvider.nowClass, p.dataType)
        // generate param access helper
        attributeReader(p.id, p.dataType, isNullable = false)
        s"$n: ${nativeType.paramType}"
      }, "", ", ", "")

      out.puts(s"impl<$readLife, $streamLife: $readLife> ${classTypeName(typeProvider.nowClass)} {")
      out.inc
      out.puts(s"pub fn set_params(&mut self, $paramsArg) {")
      out.inc
      typeProvider.nowClass.params.foreach(p => handleAssignmentParams(p.id, paramName(p.id)))
      out.dec
      out.puts("}")
      out.dec
      out.puts("}")
    }
    typeProvider.nowClass.meta.endian match {
      case Some(_: CalcEndian) | Some(InheritedEndian) =>
        out.puts(s"impl<$readLife, $streamLife: $readLife> ${classTypeName(typeProvider.nowClass)} {")
        out.inc
        val nativeType = kaitaiTypeToNativeType( Some(EndianIdentifier),
                                        typeProvider.nowClass,
                                        IntMultiType(signed = true, Width4, None),
                                        TypeKind.Raw)
        out.puts(s"pub fn set_endian(&self, ${idToStr(EndianIdentifier)}: ${nativeType.nativeType}) {")
        out.inc
        handleAssignmentSimple(EndianIdentifier, s"${idToStr(EndianIdentifier)}")
        out.dec
        out.puts("}")
        out.dec
        out.puts("}")
      case _ =>
    }
    out.puts(s"impl<$readLife, $streamLife: $readLife> ${classTypeName(typeProvider.nowClass)} {")
    out.inc
    out.puts(
      s"""|fn get_root<'a>(&'a self, _root: Option<&'a ${type2class(className.head)}>) -> Option<&'a ${type2class(className.head)}> {
          |        match _root  {
          |            Some(_p) => _root,
          |            None => Some(self._root.as_ref().unwrap().as_ref()),
          |        }
          |    }""".stripMargin)
  }

  override def universalFooter: Unit = {
    out.dec
    out.puts("}")
  }

  override def instanceDeclaration(attrName: InstanceIdentifier,
                                   attrType: DataType,
                                   isNullable: Boolean): Unit = {
    val nativeType = kaitaiTypeToNativeType(Some(attrName), typeProvider.nowClass, attrType)
    out.puts(s"${calculatedFlagForName(attrName)}: Cell<bool>,")
    out.puts(s"${idToStr(attrName)}: ${nativeType.attrType},")
  }

  def calculatedFlagForName(ksName: Identifier) =
  s"f_${idToStr(ksName)}"

  override def instanceClear(instName: InstanceIdentifier): Unit = {
    var set = false
    val ins = translator.get_instance(typeProvider.nowClass, idToStr(instName))
    if (ins.isDefined) {
      set = ins.get.dataTypeComposite match {
        case _: UserType => true
        case _ => false
      }
    }
    if (!set) {
      out.puts(s"self.${calculatedFlagForName(instName)}.set(false);")
    }
  }

  override def instanceSetCalculated(instName: InstanceIdentifier): Unit = {
    var set = false
    val ins = translator.get_instance(typeProvider.nowClass, idToStr(instName))
    if (ins.isDefined) {
      set = ins.get.dataTypeComposite match {
        case _: UserType => true
        case _ => false
      }
    }
    if (!set) {
      out.puts(s"self.${calculatedFlagForName(instName)}.set(true);")
    }
  }

  override def idToStr(id: Identifier): String = RustCompiler.idToStr(id)

  override def instanceHeader(className: List[String],
                              instName: InstanceIdentifier,
                              dataType: DataType,
                              isNullable: Boolean): Unit = {
    in_instance = true
    out.puts(s"pub fn ${idToStr(instName)}<S: $kstreamName>(")
    out.inc
    out.puts("&self,")
    out.puts(s"${privateMemberName(IoIdentifier)}: &$streamLife S,")
    out.puts(s"${privateMemberName(RootIdentifier)}: Option<&${classTypeName(typeProvider.topClass)}>")
    out.dec
    val nativeType = kaitaiTypeToNativeType(Some(instName), typeProvider.nowClass, dataType)
    out.puts(s") -> KResult<${nativeType.resType}> {")
    out.inc
  }

  override def instanceCheckCacheAndReturn(instName: InstanceIdentifier,
                                           dataType: DataType): Unit = {
    out.puts(s"if self.${calculatedFlagForName(instName)}.get() {")
    out.inc
    out.puts(s"return Ok(${privateMemberName(instName)}.borrow());")
    out.dec
    out.puts("}")
  }

  var in_instance = false

  override def instanceCalculate(instName: Identifier, dataType: DataType, value: Ast.expr): Unit = {
    dataType match {
      case _: UserType =>
        out.puts(s"*${privateMemberName(instName)}.borrow_mut() = ${translator.remove_deref(expression(value))}.clone();")
      case _: StrType =>
        out.puts(s"*${privateMemberName(instName)}.borrow_mut() = ${translator.remove_deref(expression(value))}.to_string();")
      case _: BytesType =>
        out.puts(s"*${privateMemberName(instName)}.borrow_mut() = ${translator.rem_vec_amp(translator.remove_deref(expression(value)))}.to_vec();")
      case _: ArrayType =>
        out.puts(s"*${privateMemberName(instName)}.borrow_mut() = ${translator.rem_vec_amp(translator.remove_deref(expression(value)))}.to_vec();")
      case _: EnumType =>
        out.puts(s"*${privateMemberName(instName)}.borrow_mut() = ${translator.remove_deref(expression(value))};")
      case _ =>
        translator.context_need_deref_attr = true
        val primType = kaitaiPrimitiveToNativeType(dataType)
        out.puts(s"*${privateMemberName(instName)}.borrow_mut() = (${expression(value)}) as $primType;")
        translator.context_need_deref_attr = false
    }
  }

  override def instanceReturn(instName: InstanceIdentifier,
                              attrType: DataType): Unit = {
    out.puts(s"Ok(${privateMemberName(instName)}.borrow())")
    in_instance = false
  }

  override def enumDeclaration(curClass: List[String],
                               enumName: String,
                               enumColl: Seq[(Long, EnumValueSpec)]): Unit = {

    val enumClass = types2class(curClass ::: List(enumName))

    // Set up the actual enum definition
    out.puts(s"#[derive(Debug, PartialEq, Clone)]")
    out.puts(s"pub enum $enumClass {")
    out.inc

    enumColl.foreach {
      case (_, label) =>
        if (label.doc.summary.isDefined)
          universalDoc(label.doc)

        out.puts(s"${type2class(label.name)},")
    }
    out.puts("Unknown(i64),")

    out.dec
    out.puts("}")
    out.puts

    // Set up parsing enums from the underlying value
    out.puts(s"impl TryFrom<i64> for $enumClass {")

    out.inc
    // We typically need the lifetime in KError for returning byte slices from stream;
    // because we can only return `UnknownVariant` which contains a Copy type, it's safe
    // to declare that the error type is `'static`
    out.puts(s"type Error = KError;")
    out.puts(s"fn try_from(flag: i64) -> KResult<$enumClass> {")

    out.inc
    out.puts(s"match flag {")

    out.inc
    enumColl.foreach {
      case (value, label) =>
        out.puts(s"$value => Ok($enumClass::${type2class(label.name)}),")
    }
    out.puts(s"_ => Ok($enumClass::Unknown(flag)),")
    out.dec

    out.puts("}")
    out.dec
    out.puts("}")
    out.dec
    out.puts("}")
    out.puts

    out.puts(s"impl From<&$enumClass> for i64 {")
    out.inc
    out.puts(s"fn from(val: &$enumClass) -> Self {")
    out.inc
    out.puts(s"match val {")
    out.inc
    enumColl.foreach {
      case (value, label) =>
        out.puts(s"$enumClass::${type2class(label.name)} => $value,")
    }
    out.puts(s"$enumClass::Unknown(v) => *v")
    out.dec
    out.puts("}")
    out.dec
    out.puts("}")
    out.dec
    out.puts("}")
    out.puts

    out.puts(s"impl Default for $enumClass {")
    out.inc
    out.puts(s"fn default() -> Self { $enumClass::Unknown(0) }")
    out.dec
    out.puts("}")
    out.puts
  }

  override def universalDoc(doc: DocSpec): Unit = {
    out.puts
    out.puts( "/**")

    doc.summary.foreach(docStr => out.putsLines(" * ", docStr))

    doc.ref.foreach {
      case TextRef(text) =>
        out.putsLines(" * ", s"\\sa $text")
      case UrlRef(url, text) =>
        out.putsLines(" * ", s"\\sa $url $text")
    }

    out.puts( " */")
  }

  override def handleAssignmentRepeatExpr(id: Identifier, expr: String): Unit =
    handleAssignmentRepeatEos(id, expr)

  def handleAssignmentParams(id: Identifier, expr: String): Unit = {
    val paramId = typeProvider.nowClass.params.find(s => s.id == id)
    val need_clone = if (paramId.isDefined) !RustTranslator.is_copy_type(paramId.get.dataType) else false
    val member = privateMemberName(id)
    val nativeType = kaitaiTypeToNativeType(Some(id), typeProvider.nowClass, paramId.get.dataType)
    nativeType.kind match {
      case TypeKind.RefCell =>
        out.puts(s"$member = RefCell::new($expr.clone());")
      case TypeKind.ParamBox =>
        out.puts(s"*$member.borrow_mut() = Some(Box::new($expr.clone()));")
      case TypeKind.Option =>
        out.puts(s"*$member.borrow_mut() = Some($expr.clone());")
      case _ =>
        if (need_clone)
          out.puts(s"$member = $expr.clone();")
        else
          out.puts(s"$member = $expr;")
    }
//    if (nativeType.kind == TypeKind.RefCell)
//      out.puts(s"$member = RefCell::new($expr.clone());")
//    else {
//      paramId.get.dataType match {
//        case _: EnumType =>
//          out.puts(s"$member = Some($expr.clone());")
//        case _ =>
//          if (need_clone)
//            out.puts(s"$member = $expr.clone();")
//          else
//            out.puts(s"$member = $expr;")
//      }
//    }
  }

  override def handleAssignmentSimple(id: Identifier, expr: String): Unit = {
    val seqId = typeProvider.nowClass.seq.find(s => s.id == id)
    var done = false
    var refcell = false
    var opaque = false
    if (seqId.isDefined) {
      val idType = seqId.get.dataType
      idType match {
        case t: UserType =>
          refcell = true
          if (t.isOpaque) {
            opaque = true
          }
        case _: UserType | _: BytesType | _: ArrayType | _: StrType | _: NumericType | _: BooleanType=>
          refcell = true
        case _: EnumType =>
          done = true
          out.puts(
            s"*${privateMemberName(id)}.borrow_mut() = $expr;"
          )
        case _: SwitchType =>
          done = true
          out.puts(s"*${privateMemberName(id)}.borrow_mut() = Some($expr);")
        case _ =>
      }
      if (refcell) {
          val nativeType = kaitaiTypeToNativeType(Some(id), typeProvider.nowClass, idType)
          if (nativeType.kind == TypeKind.RefCell) {
            if (opaque) {
              out.puts(s"*${privateMemberName(id)}.borrow_mut() = Some(Box::new($expr));")
            } else {
              out.puts(s"*${privateMemberName(id)}.borrow_mut() = $expr;")
            }
            done = true
          }
      }
    }
    if (!done) {
      var inst = false
      id match {
        case _: InstanceIdentifier =>
          inst = true
        case RawIdentifier(inner) => inner match {
          case _: InstanceIdentifier =>
            inst = true
          case _ =>
        }
//        case EndianIdentifier =>
//          inst = true
        case _ =>
      }
      if (inst) {
        val member = translator.findMember(idToStr(id))
        if (member.isDefined) {
          val nativeType = kaitaiTypeToNativeType(Some(id), typeProvider.nowClass, member.get.dataTypeComposite)
          if (nativeType.kind == TypeKind.ParamBox) {
            done = true
            out.puts(s"*${privateMemberName(id)}.borrow_mut() = Some(Box::new($expr));")
          }
        }
      }
    }
    if (!done)
      out.puts(s"*${privateMemberName(id)}.borrow_mut() = $expr;")
  }

  override def handleAssignmentTempVar(dataType: DataType, id: String, expr: String): Unit =
    out.puts(s"let $id = $expr;")

  override def parseExpr(dataType: DataType,
                         assignType: DataType,
                         io: String,
                         defEndian: Option[FixedEndian]): String = {
    var addParams = ""
    var result = "t"
    val expr = dataType match {
      case t: ReadableType =>
        t match {
          case IntMultiType(_, _, None) =>
            s"if *${privateMemberName(EndianIdentifier)}.borrow() == 1 { $io.read_${t.apiCall(Some(LittleEndian))}()?.into() } else { $io.read_${t.apiCall(Some(BigEndian))}()?.into() }"
          case IntMultiType(_, _, Some(e)) =>
            s"$io.read_${t.apiCall(Some(e))}()?.into()"
          case _ =>
            s"$io.read_${t.apiCall(defEndian)}()?.into()"
        }
      case _: BytesEosType =>
        result = "t.to_vec()"
        s"$io.read_bytes_full()?"
      case b: BytesTerminatedType =>
        result = "t.to_vec()"
        s"$io.read_bytes_term(${b.terminator}, ${b.include}, ${b.consume}, ${b.eosError})?"
      case b: BytesLimitType =>
        result = "t.to_vec()"
        s"$io.read_bytes(${expression(b.size)} as usize)?"
      case BitsType1(bitEndian) => s"$io.read_bits_int_${bitEndian.toSuffix}(1)? != 0"
      case BitsType(width: Int, bitEndian) => s"$io.read_bits_int_${bitEndian.toSuffix}($width)?"
      case t: UserType =>
        addParams = Utils.join(t.args.map{ a =>
          val typ = translator.detectType(a)
          var byref = ""
          val nativeType = kaitaiTypeToNativeType(None, typeProvider.nowClass, typ)
          var try_into = ""
          // exclude enums
          typ match {
            case _: NumericType => try_into = s".try_into().map_err(|_| KError::CastError)?"
            case _: EnumType =>
            case _ =>
              if ((nativeType.kind != TypeKind.ParamBox) && !RustTranslator.is_copy_type(typ))
                byref = "&"
          }
          var need_deref = ""
          if (nativeType.kind == TypeKind.RefCell)
            need_deref = "&*"
          s"$byref$need_deref${translator.translate(a)}$try_into"
        }, "", ", ", "")
        val userType = t match {
          case t: UserType =>
            val baseName = t.classSpec match {
              case Some(spec) => types2class(spec.name)
              case None => types2class(t.name)
            }
            s"$baseName"
        }
        val addArgs = if (t.isOpaque) {
          ", None, None"
        } else {
          val currentType = classTypeName(typeProvider.nowClass)
          val root = if (typeProvider.nowClass.isTopLevel) {
            "Some(self)"
          } else {
            privateMemberName(RootIdentifier)
          }
          val parent = t.forcedParent match {
            case Some(USER_TYPE_NO_PARENT) => "None"
            case Some(fp) => translator.translate(fp)
            case None =>
              if ((userType contains currentType) && !in_instance) {
                if (typeProvider.nowClass.isTopLevel) {
                  s"Some(${privateMemberName(ParentIdentifier)}.unwrap_or(KStructUnit::parent_stack()).push(self))"
                } else {
                  s"Some(${privateMemberName(ParentIdentifier)}.unwrap().push(self))"
                }
              } else {
                if(in_instance) {
                  s"None"
                } else {
                  s"${privateMemberName(ParentIdentifier)}"
                }
              }
          }
          s", $root, $parent"
        }
        val streamType = if (io == privateMemberName(IoIdentifier)) {
          "S"
        } else {
          "BytesReader"
        }
        if (addParams.isEmpty) {
          if (t.classSpec.isDefined) t.classSpec.get.meta.endian match {
            case Some(InheritedEndian) =>
              out.puts(s"let mut t = $userType::default();")
              out.puts(s"t.set_endian(*${privateMemberName(EndianIdentifier)}.borrow());")
              out.puts(s"t.read::<$streamType>($io$addArgs)?;")
            case _ =>
              out.puts(s"let t = Self::read_into::<$streamType, $userType>($io$addArgs)?.into();")
          }
        } else {
          //val at = kaitaiTypeToNativeType(None, typeProvider.nowClass, assignType, excludeOptionWrapper = true)
          out.puts(s"let mut t = $userType::default();")
          out.puts(s"t.set_params($addParams);")
          out.puts(s"t.read::<$streamType>($io$addArgs)?;")
        }
        return s"t"
      case _ => s"// parseExpr($dataType, $assignType, $io, $defEndian)"
    }
    // in expr_2.ksy we got into rustc bug
    // https://github.com/rust-lang/rust/issues/82656
    // https://github.com/rust-lang/rust/issues/70919
    // workaround:
    out.puts(s"let t = $expr;")
    result
  }

  override def bytesPadTermExpr(expr0: String,
                                padRight: Option[Int],
                                terminator: Option[Int],
                                include: Boolean): String = {
    val ioId = privateMemberName(IoIdentifier)
    val expr = padRight match {
      case Some(p) => s"$ioId.bytes_strip_right($expr0.as_slice(), $p).into()"
      case None => expr0
    }

    terminator match {
      case Some(term) =>
        if (!expr.endsWith(".into()"))
          s"$ioId.bytes_terminate($expr.as_slice(), $term, $include).into()"
        else
          s"$ioId.bytes_terminate($expr, $term, $include).into()"
      case None =>
        expr
    }
  }

  override def attrFixedContentsParse(attrName: Identifier,
                                      contents: String): Unit =
    out.puts(s"// attrFixedContentsParse($attrName, $contents)")

  override def publicMemberName(id: Identifier): String =
    s"// publicMemberName($id)"

  override def localTemporaryName(id: Identifier): String =
    s"_t_${idToStr(id)}"

  override def userTypeDebugRead(id: String, dataType: DataType, assignType: DataType): Unit = {
    // we already have splitted construction of object and read method
  }

  override def switchRequiresIfs(onType: DataType): Boolean = onType match {
    case _: IntType | _: EnumType => false
    case _ => true
  }

  override def switchStart(id: Identifier, on: Ast.expr): Unit = {
    switch_else_exist = false
    out.puts(s"match ${expression(on)} {")
    out.inc
  }

  override def switchCaseStart(condition: Ast.expr): Unit = {
    out.puts(s"${expression(condition)} => {")
    out.inc
  }

  override def switchCaseEnd(): Unit = {
    out.dec
    out.puts("}")
  }

  var switch_else_exist = false

  override def switchElseStart(): Unit = {
    switch_else_exist = true
    out.puts("_ => {")
    out.inc
  }

  override def switchEnd(): Unit = {
    if (!switch_else_exist) {
      out.puts("_ => {}")
    }
    out.dec
    out.puts("}")
  }

  override def switchIfStart(id: Identifier, on: Ast.expr, onType: DataType): Unit = {
    out.puts("{")
    out.inc
    out.puts(s"let on = &${expression(on)};")
  }

  override def switchIfCaseFirstStart(condition: Ast.expr): Unit = {
    out.puts(s"if on.as_slice() == ${expression(condition)} {")
    out.inc
  }

  override def switchIfCaseStart(condition: Ast.expr): Unit = {
    out.puts(s"else if on.as_slice() == ${expression(condition)} {")
    out.inc
  }

  override def switchIfCaseEnd(): Unit = {
    out.dec
    out.puts("}")
  }

  override def switchIfElseStart(): Unit = {
    out.puts("else {")
    out.inc
  }

  override def switchIfEnd(): Unit = {
    out.dec
    out.puts("}")
  }

  override def allocateIO(id: Identifier, rep: RepeatSpec): String = {//= privateMemberName(IoIdentifier)
    val memberName = privateMemberName(id)
    val ioId = IoStorageIdentifier(id)

    var newStreamRaw = s"$memberName"
    val ioName = rep match {
      case NoRepeat =>
        var newStream = newStreamRaw
        val localIO = localTemporaryName(ioId)
        if (in_instance) {
          val ids = idToStr(id)
          out.puts(s"let $ids = $newStream.borrow();")
          newStream = ids
        }
        out.puts(s"let slice_holder = &$newStream.borrow()[..];")
        out.puts(s"let $localIO = BytesReader::new(slice_holder);")
        s"&$localIO"
      case _ =>
        val ids = idToStr(id)
        val localIO = s"io_$ids"
        if (in_instance) {
          out.puts(s"let $ids = $newStreamRaw.borrow();")
          newStreamRaw = ids
        }
        out.puts(s"let slice_holder = &$newStreamRaw.last().borrow()[..];")
        out.puts(s"let $localIO = BytesReader::new(slice_holder);")
        s"&$localIO"
    }

    ioName
  }

  def switchTypeEnum(id: Identifier, st: SwitchType): Unit = {
    // Because Rust can't handle `AnyType` in the type hierarchy,
    // we generate an enum with all possible variations
    val enum_typeName = kaitaiTypeToNativeType(Some(id), typeProvider.nowClass, st).nativeType
    out.puts("#[derive(Debug, PartialEq, Clone)]")
    out.puts(s"pub enum $enum_typeName {")
    out.inc
    out.puts("__NOT_INITED__,")

    val types = st.cases.values.toSet

    {
      val types_set = scala.collection.mutable.Set[String]()
      types.foreach(t => {
        // Because this switch type will itself be in an option, we can exclude it from user types
        val variantName = switchVariantName(id, t)
        val typeName = kaitaiTypeToNativeType(Some(id), typeProvider.nowClass, t).nativeType
        val new_typename = types_set.add(typeName)
        // same typename could be in case of different endianness
        if (new_typename) {
          out.puts(s"$variantName($typeName),")
        }
      })
    }

    out.dec
    out.puts("}")

    out.puts(s"""impl Default for $enum_typeName {
                 |    fn default() -> Self { $enum_typeName::__NOT_INITED__ }
                 |}""".stripMargin)

    var enum_only_numeric = true
    types.foreach {
      case _: NumericType => // leave true
      case _ => enum_only_numeric = false
    }

    // generate only if switch types are different
    {
      val types_set = scala.collection.mutable.Set[String]()
      // add helper methods From
      types.foreach(t => {
        // Because this switch type will itself be in an option, we can exclude it from user types
        val variantName = switchVariantName(id, t)
        var v = "v"
        val typeName = t match {
          case _: BytesType =>
            v = "v.to_vec()"
            s"&[u8]" // special case for Bytes(Vec[u8]) (else switch)
          case _ => kaitaiTypeToNativeType(Some(id), typeProvider.nowClass, t).nativeType
        }
        val new_typename = types_set.add(typeName)
        if (new_typename) {
          out.puts(s"impl From<$typeName> for $enum_typeName {")
          out.inc
          out.puts(s"fn from(v: $typeName) -> Self {")
          out.inc
          out.puts(s"Self::$variantName($v)")
          out.dec
          out.puts("}")
          out.dec
          out.puts("}")
          if (enum_only_numeric) {
            out.puts(s"impl From<&$enum_typeName> for $typeName {")
            out.inc
            out.puts(s"fn from(e: &$enum_typeName) -> Self {")
            out.inc
            out.puts(s"if let $enum_typeName::$variantName(v) = e {")
            out.inc
            out.puts(s"return *v")
            out.dec
            out.puts("}")
            out.puts(s"""panic!(\"trying to convert from enum $enum_typeName::$variantName to $typeName, enum value {:?}\", e)""")
            out.dec
            out.puts("}")
            out.dec
            out.puts("}")
          }
        }
      })
    }
    if (enum_only_numeric) {
      out.puts(s"impl From<&$enum_typeName> for usize {")
      out.inc
      out.puts(s"fn from(e: &$enum_typeName) -> Self {")
      out.inc
      out.puts(s"match e {")
      out.inc
      val variants_set = scala.collection.mutable.Set[String]()
      types.foreach(t => {
        val variantName = switchVariantName(id, t)
        val new_typename = variants_set.add(variantName)
        if (new_typename) {
          out.puts(s"$enum_typeName::$variantName(v) => *v as usize,")
        }
      })
      out.dec
      out.puts("}")
      out.dec
      out.puts("}")
      out.dec
      out.puts("}")
      out.puts
    }
  }

  def switchVariantName(id: Identifier, attrType: DataType): String =
    attrType match {
      // TODO: Not exhaustive
      case Int1Type(false) => "U1"
      case IntMultiType(false, Width2, _) => "U2"
      case IntMultiType(false, Width4, _) => "U4"
      case IntMultiType(false, Width8, _) => "U8"

      case Int1Type(true) => "S1"
      case IntMultiType(true, Width2, _) => "S2"
      case IntMultiType(true, Width4, _) => "S4"
      case IntMultiType(true, Width8, _) => "S8"

      case FloatMultiType(Width4, _) => "F4"
      case FloatMultiType(Width8, _) => "F8"

      case BitsType(_,_) => "Bits"
      case _: BooleanType => "Boolean"
      case CalcIntType => "Int"
      case CalcFloatType => "Float"
      case _: StrType => "String"
      case _: BytesType => "Bytes"

      case t: UserType =>
        kaitaiTypeToNativeType(Some(id), typeProvider.nowClass, t).nativeType
      case t: EnumType =>
        kaitaiTypeToNativeType(Some(id), typeProvider.nowClass, t).nativeType
      case t:
        ArrayType => s"Arr${switchVariantName(id, t.elType)}"
      case _ =>
        ???
    }

  override def ksErrorName(err: io.kaitai.struct.datatype.KSError): String =
    s"KaitaiStream.$err"

  override def attrValidateExpr(
    attrId: Identifier,
    attrType: DataType,
    checkExpr: Ast.expr,
    err: KSError,
    errArgs: List[Ast.expr]
  ): Unit = {
    val errArgsStr = errArgs.map(translator.translate).mkString(", ")
    out.puts(s"if !(${expression(checkExpr)}) {")
    out.inc
    out.puts(s"""return Err(KError::ValidationNotEqual(r#"$errArgsStr"#.to_string()));""")
    out.dec
    out.puts("}")
  }

  override def attrParse2(
                           id: Identifier,
                           dataType: DataType,
                           io: String,
                           rep: RepeatSpec,
                           isRaw: Boolean,
                           defEndian: Option[FixedEndian],
                           assignTypeOpt: Option[DataType] = None
                         ): Unit = {
    dataType match {
      case t: EnumType =>
        val expr =
          t.basedOn match {
            case inst: ReadableType =>
              s"($io.read_${inst.apiCall(defEndian)}()? as i64).try_into()?"
            case BitsType(width: Int, bitEndian) =>
              s"($io.read_bits_int_${bitEndian.toSuffix}($width)? as i64).try_into()?"
            case _ =>
              s"${idToStr(id)} - t.basedOn ???"
          }
        handleAssignment(id, expr, rep, isRaw)
      case _ =>
        super.attrParse2(id, dataType, io, rep, isRaw, defEndian, assignTypeOpt)
    }
  }

  override def classToString(toStringExpr: Ast.expr): Unit = {
    importList.add("use std::fmt;")
    out.puts(s"impl fmt::Display for ${classTypeName(typeProvider.nowClass)} {")
    out.inc
    out.puts(s"fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {")
    out.inc
    out.puts(s"""write!(f, "{}", ${translator.translate(toStringExpr)})""")
    out.dec
    out.puts("}")
    out.dec
    out.puts("}")
  }
}

object RustCompiler
  extends LanguageCompilerStatic
    with StreamStructNames
    with UpperCamelCaseClasses {
  override def getCompiler(tp: ClassTypeProvider,
                           config: RuntimeConfig): LanguageCompiler =
    new RustCompiler(tp, config)

  override def kstreamName = "KStream"

  def privateMemberName(id: Identifier): String = id match {
    case IoIdentifier => "_io"
    case RootIdentifier => "_root"
    case ParentIdentifier => "_parent"
    case _ => s"self.${idToStr(id)}"
  }

  def idToStr(id: Identifier): String = id match {
    case SpecialIdentifier(n) => n
    case NamedIdentifier(n) => n
    case InstanceIdentifier(n) => n
    case NumberedIdentifier(idx) => s"${NumberedIdentifier.TEMPLATE}$idx"
    case RawIdentifier(inner) => s"${idToStr(inner)}_raw" // use suffix naming, easy to replace, like in anyField()
    case IoStorageIdentifier(inner) => s"${idToStr(inner)}_io" // same here
  }

  @tailrec
  def rootClassTypeName(c: ClassSpec, isRecurse: Boolean = false): String = {
    if (!isRecurse && c.isTopLevel)
      "Self"
    else if (c.isTopLevel)
      classTypeName(c)
    else
      rootClassTypeName(c.upClass.get, isRecurse = true)
  }

  def parentStackTypeName(c: ClassSpec): String = {
    if (c.isTopLevel)
      s"$kstructUnitName"
    else
      s"(&$readLife ${classTypeName(c.upClass.get)}, <${classTypeName(c.upClass.get)} as $kstructName<$readLife, $streamLife>>::ParentStack)"
  }

  override def kstructName = s"KStruct"

  def readLife = "'r"

  def kstructUnitName = "KStructUnit"

  def classTypeName(c: ClassSpec): String =
    s"${types2class(c.name)}"

  def streamLife = "'s"

  def types2class(names: List[String]): String =
  // TODO: Use `mod` to scope types instead of weird names
    names.map(x => type2class(x)).mkString("_")

  def lifetimeParam(d: DataType): String =
    if (containsReferences(d)) s"<$streamLife>" else ""

  def containsReferences(d: DataType): Boolean = containsReferences(d, None)

  def containsReferences(c: ClassSpec,
                         originating: Option[ClassSpec]): Boolean =
    c.seq.exists(t => containsReferences(t.dataType, originating)) ||
      c.instances.exists(
        i => containsReferences(i._2.dataTypeComposite, originating)
      )

  def containsReferences(d: DataType, originating: Option[ClassSpec]): Boolean =
    d match {
      case _: BytesType | _: StrType => true
      case _: UserType => true
      /*
      t.classSpec match {
        // Recursive types may need references, but the recursion itself
        // will be handled by `Box<>`, so doesn't need a reference
        case Some(inner) if originating.contains(inner) => false
        case Some(inner) => containsReferences(inner, originating.orElse(Some(inner)))
        case None => false
      }
       */
      case t: ArrayType => containsReferences(t.elType, originating)
      case st: SwitchType =>
        st.cases.values.exists(t => containsReferences(t, originating))
      case _ => false
    }

  object TypeKind extends Enumeration {
    type TypeKind = Value
    val None, Raw, Option, RefCell, Param, ParamBox = Value
  }

  case class NativeType(nativeType: String, kind: TypeKind.Value, dataType: DataType) {
    def attrGetterDcl(fnName: String): String = {
      kind match {
        case TypeKind.RefCell =>
          s"pub fn $fnName(&self) -> Ref<$nativeType> {"
        case TypeKind.Param =>
          s"pub fn $fnName(&self) -> pt::Ref<$nativeType> {"
        case TypeKind.ParamBox =>
          s"pub fn $fnName(&self) -> $nativeType {"
        case TypeKind.Raw =>
          s"pub fn $fnName(&self) -> $nativeType {"
        case _ =>
          s"pub fn $fnName(&self) -> &$nativeType {"
      }
    }

    def attrGetterImpl(attrName: String) : String = {
      kind match {
        case TypeKind.RefCell =>
          s"self.$attrName.borrow()"
        case TypeKind.Param =>
          s"self.$attrName.borrow()"
        case TypeKind.ParamBox =>
          s"self.$attrName.borrow().as_ref().unwrap().as_ref().clone()"
        case TypeKind.Option =>
          s"self.$attrName.as_ref().unwrap()"
        case TypeKind.Raw =>
          s"self.$attrName"
        case _ =>
          s"&self.$attrName"
      }
    }

    def attrType: String = {
      kind match {
        case TypeKind.RefCell =>
          s"RefCell<$nativeType>"
        case TypeKind.Param =>
          s"ParamType<$nativeType>"
        case TypeKind.ParamBox =>
          s"ParamType<Box<$nativeType>>"
        case TypeKind.Option =>
          s"Option<$nativeType>"
        case _ =>
          val byref = if (!RustTranslator.is_copy_type(dataType)) "&" else ""
          s"$byref$nativeType"
      }
    }

    def paramType: String = {
      kind match {
        case TypeKind.RefCell =>
          s"Ref<$nativeType>"
        case TypeKind.ParamBox =>
          s"&$nativeType"
        case _ =>
          val byref = if (!RustTranslator.is_copy_type(dataType)) "&" else ""
          s"$byref$nativeType"
      }
    }

    def resType: String = {
      kind match {
        case TypeKind.RefCell =>
          s"Ref<$nativeType>"
        case TypeKind.ParamBox =>
          s"pt::Ref<Box<$nativeType>>"
        case _ =>
          val byref = if (!RustTranslator.is_copy_type(dataType)) "&" else ""
          s"$byref$nativeType"
      }
    }
  }

  def kaitaiTypeToNativeType(id: Option[Identifier],
                             cs: ClassSpec,
                             attrType: DataType,
                             advisedKind: TypeKind = TypeKind.None): NativeType = {
//    def wrapRefCell(s: String): String =
//      if (excludeRefCellWrapper || s.startsWith("ParamType<")) s else s"RefCell<$s>"

    attrType match {
      // TODO: Not exhaustive
      case _: NumericType | _: BooleanType | _: StrType | _: BytesType =>
        val typeKind = if (advisedKind != TypeKind.None) advisedKind else TypeKind.RefCell
        NativeType(s"${kaitaiPrimitiveToNativeType(attrType)}", typeKind, attrType)

      case t: UserType =>
        val baseName = t.classSpec match {
          case Some(spec) => types2class(spec.name)
          case None => types2class(t.name)
        }

        NativeType(baseName, if (t.isOpaque) TypeKind.ParamBox else TypeKind.RefCell, attrType)
        // Because we can't predict if opaque types will recurse, we have to box them
//        val typeName =
//          if (!excludeBox && t.isOpaque)                    s"ParamType<Box<$baseName>>"
//          else                                              s"$baseName"
//        if (excludeOptionWrapper || excludeRefCellWrapper)  typeName
//        else                                                wrapRefCell(typeName)

      case t: EnumType =>
        val typeName = t.enumSpec match {
          case Some(spec) => s"${types2class(spec.name)}"
          case None => s"${types2class(t.name)}"
        }
        NativeType(typeName, TypeKind.RefCell, attrType)
        //if (excludeOptionWrapper) typeName else s"Option<$typeName>"

      case t: ArrayType =>
        val nativeType = kaitaiTypeToNativeType(id, cs, t.elType)
        NativeType(s"Vec<${nativeType.nativeType}>", TypeKind.RefCell, attrType)
        //wrapRefCell(s"Vec<${kaitaiTypeToNativeType(id, cs, t.elType, excludeOptionWrapper = true, excludeRefCellWrapper = true)}>")

      case _: SwitchType =>
        val typeName = id.get match {
          case name: NamedIdentifier =>
            s"${types2class(cs.name ::: List(name.name))}"
          case name: InstanceIdentifier =>
            s"${types2class(cs.name ::: List(name.name))}"
          case _ =>
            kstructUnitName
        }

        NativeType(typeName, TypeKind.Param, attrType)
        //if (excludeOptionWrapper) typeName else s"Option<$typeName>"

      case KaitaiStreamType =>
        NativeType(kstreamName, TypeKind.Raw, attrType)
      case _ =>
        ???
    }
  }

  def kaitaiPrimitiveToNativeType(attrType: DataType): String = attrType match {
    case Int1Type(false) => "u8"
    case IntMultiType(false, Width2, _) => "u16"
    case IntMultiType(false, Width4, _) => "u32"
    case IntMultiType(false, Width8, _) => "u64"

    case Int1Type(true) => "i8"
    case IntMultiType(true, Width2, _) => "i16"
    case IntMultiType(true, Width4, _) => "i32"
    case IntMultiType(true, Width8, _) => "i64"

    case FloatMultiType(Width4, _) => "f32"
    case FloatMultiType(Width8, _) => "f64"

    case BitsType(_,_) => "u64"

    case _: BooleanType => "bool"
    case CalcIntType => "i32"
    case CalcFloatType => "f64"

    case _: StrType => "String"
    case _: BytesType => "Vec<u8>"

    case ArrayTypeInStream(inType) => s"Vec<${kaitaiPrimitiveToNativeType(inType)}>"

    case _ => "kaitaiPrimitiveToNativeType ???"
  }
}
