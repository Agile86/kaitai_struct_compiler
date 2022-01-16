package io.kaitai.struct.format

import io.kaitai.struct.datatype.DataType
import io.kaitai.struct.datatype.DataType._
import io.kaitai.struct.exprlang.Ast
import io.kaitai.struct.problems.KSYParseError

import scala.collection.mutable

/**
  * Type that we use when we want to refer to a class specification or something
  * close, but not (yet) that well defined.
  */
sealed trait ClassSpecLike {
  def toDataType: DataType
}
case object UnknownClassSpec extends ClassSpecLike {
  override def toDataType: DataType = CalcKaitaiStructType
}
case object GenericStructClassSpec extends ClassSpecLike {
  override def toDataType: DataType = CalcKaitaiStructType
}

sealed trait Sized
case object DynamicSized extends Sized
case object NotCalculatedSized extends Sized
case object StartedCalculationSized extends Sized
case class FixedSized(n: Int) extends Sized

case class ClassSpec(
  fileName: Option[String],
  path: List[String],
  isTopLevel: Boolean,
  meta: MetaSpec,
  doc: DocSpec,
  toStringExpr: Option[Ast.expr],
  params: List[ParamDefSpec],
  seq: List[AttrSpec],
  types: Map[String, ClassSpec],
  instances: Map[InstanceIdentifier, InstanceSpec],
  enums: Map[String, EnumSpec]
) extends ClassSpecLike with YAMLPath {
  var parentClass: ClassSpecLike = UnknownClassSpec

  /**
    * Full absolute name of the class (including all names of classes that
    * it's nested into, as a namespace). Derived either from `meta`/`id`
    * (for top-level classes), or from keys in `types` (for nested classes).
    */
  var name = List[String]()

  /**
    * @return Absolute name of class as string, components separated by
    *         double colon operator `::`
    */
  def nameAsStr: String = name.mkString("::")

  /**
    * @return Name of the file this type originates from, or, worst case,
    *         if filename is unknown, name of the type.
    */
  def fileNameAsStr: String = fileName.getOrElse(nameAsStr)

  /**
    * The class specification that this class is nested into, if it exists.
    * For top-level classes, it's None.
    */
  var upClass: Option[ClassSpec] = None

  var seqSize: Sized = NotCalculatedSized

  def toDataType: DataType = {
    val cut = CalcUserType(name, None)
    cut.classSpec = Some(this)
    cut
  }

  def parentType: DataType = parentClass.toDataType

  /**
    * Recursively traverses tree of types starting from this type, calling
    * certain function for every type, starting from this one.
    *
    * @param proc function to execute on every encountered type.
    */
  def forEachRec(proc: (ClassSpec) => Unit): Unit = {
    proc.apply(this)
    types.foreach { case (_, typeSpec) =>
      typeSpec.forEachRec(proc)
    }
  }

  /**
    * Recursively traverses tree of types starting from this type, calling
    * certain function for every type, starting from this one.
    *
    * @param proc function to execute on every encountered type.
    * @tparam R mandates that function must return a list of this type.
    */
  def mapRec[R](proc: (ClassSpec) => Iterable[R]): Iterable[R] = {
    val r1 = proc.apply(this)
    val r2 = types.flatMap { case (_, typeSpec) =>
      typeSpec.mapRec(proc)
    }
    r1 ++ r2
  }

  override def equals(obj: Any): Boolean = obj match {
    case other: ClassSpec =>
      path == other.path &&
      isTopLevel == other.isTopLevel &&
      meta == other.meta &&
      doc == other.doc &&
      params == other.params &&
      seq == other.seq &&
      types == other.types &&
      instances == other.instances &&
      enums == other.enums &&
      name == other.name
    case _ => false
  }
}

object ClassSpec {
  val LEGAL_KEYS = Set(
    "meta",
    "doc",
    "doc-ref",
    "to-string",
    "params",
    "seq",
    "types",
    "instances",
    "enums"
  )

  def fromYaml(src: yamlesque.Node, fileName: Option[String], path: List[String], metaDef: MetaSpec): ClassSpec = {
    val srcMap = ParseUtils.asMapStr(src, path)
    ParseUtils.ensureLegalKeys(srcMap, LEGAL_KEYS, path)

    val metaPath = path ++ List("meta")
    val explicitMeta = srcMap.obj.get("meta").map(MetaSpec.fromYaml(_, metaPath)).getOrElse(MetaSpec.emptyWithPath(metaPath))
    val meta = explicitMeta.fillInDefaults(metaDef)

    val doc = DocSpec.fromYaml(srcMap, path)

    val toStringExpr = ParseUtils.getOptValueExpression(srcMap, "to-string", path)

    val params: List[ParamDefSpec] = srcMap.obj.get("params") match {
      case Some(value) => paramDefFromYaml(value, path ++ List("params"))
      case None => List()
    }
    val seq: List[AttrSpec] = srcMap.obj.get("seq") match {
      case Some(value) => seqFromYaml(value, path ++ List("seq"), meta)
      case None => List()
    }
    val types: Map[String, ClassSpec] = srcMap.obj.get("types") match {
      case Some(value) => typesFromYaml(value, fileName, path ++ List("types"), meta)
      case None => Map()
    }
    val instances: Map[InstanceIdentifier, InstanceSpec] = srcMap.obj.get("instances") match {
      case Some(value) => instancesFromYaml(value, path ++ List("instances"), meta)
      case None => Map()
    }
    val enums: Map[String, EnumSpec] = srcMap.obj.get("enums") match {
      case Some(value) => enumsFromYaml(value, path ++ List("enums"))
      case None => Map()
    }

    checkDupSeqInstIds(seq, instances)

    val cs = ClassSpec(
      fileName, path, path.isEmpty,
      meta, doc, toStringExpr,
      params, seq, types, instances, enums
    )

    // If that's a top-level class, set its name from meta/id
    if (path.isEmpty) {
      explicitMeta.id match {
        case None =>
          throw KSYParseError.withText("no `meta/id` encountered in top-level class spec", path ++ List("meta", "id"))
        case Some(id) =>
          cs.name = List(id)
      }
    }

    cs
  }

  def paramDefFromYaml(src: yamlesque.Node, path: List[String]): List[ParamDefSpec] = {
    src match {
      case yamlesque.Arr(srcList) =>
        val params = srcList.zipWithIndex.map { case (attrSrc, idx) =>
          ParamDefSpec.fromYaml(attrSrc, path ++ List(idx.toString), idx)
        }
        // FIXME: checkDupSeqIds(params)
        params.toList
      case unknown =>
        throw KSYParseError.withText(s"expected array, found $unknown", path)
    }
  }

  def seqFromYaml(src: yamlesque.Node, path: List[String], metaDef: MetaSpec): List[AttrSpec] = {
    src match {
      case yamlesque.Arr(srcList)  =>
        val seq = srcList.zipWithIndex.map { case (attrSrc, idx) =>
          AttrSpec.fromYaml(attrSrc, path ++ List(idx.toString), metaDef, idx)
        }
        checkDupSeqIds(seq)
        seq.toList
      case unknown =>
        throw KSYParseError.withText(s"expected array, found $unknown", path)
    }
  }

  def checkDupSeqIds(seq: Iterable[AttrSpec]): Unit = {
    val attrIds = mutable.Map[String, AttrSpec]()
    seq.foreach { (attr) =>
      attr.id match {
        case NamedIdentifier(id) =>
          checkDupId(attrIds.get(id), id, attr)
          attrIds.put(id, attr)
        case _ => // do nothing with non-named IDs
      }
    }
  }

  def checkDupSeqInstIds(seq: List[AttrSpec], instances: Map[InstanceIdentifier, InstanceSpec]): Unit = {
    val attrIds: Map[String, AttrSpec] = seq.flatMap((attr) => attr.id match {
      case NamedIdentifier(id) => Some(id -> attr)
      case _ => None
    }).toMap

    instances.foreach { case (id, instSpec) =>
      checkDupId(attrIds.get(id.name), id.name, instSpec)
    }
  }

  private def checkDupId(prevAttrOpt: Option[AttrSpec], id: String, nowAttr: YAMLPath) {
    prevAttrOpt match {
      case Some(prevAttr) =>
        throw KSYParseError.withText(
          s"duplicate attribute ID '$id', previously defined at /${prevAttr.pathStr}",
          nowAttr.path
        )
      case None =>
        // no dups, ok
    }
  }

  def typesFromYaml(src: yamlesque.Node, fileName: Option[String], path: List[String], metaDef: MetaSpec): Map[String, ClassSpec] = {
    val srcMap = ParseUtils.asMapStr(src, path)
    srcMap.obj.map { case (typeName, body) =>
      Identifier.checkIdentifierSource(typeName, "type", path ++ List(typeName))
      typeName -> ClassSpec.fromYaml(body, fileName, path ++ List(typeName), metaDef)
    }.toMap
  }

  def instancesFromYaml(src: yamlesque.Node, path: List[String], metaDef: MetaSpec): Map[InstanceIdentifier, InstanceSpec] = {
    val srcMap = ParseUtils.asMap(src, path)
    srcMap.obj.map { case (key, body) =>
      val instName = ParseUtils.asStr(key, path)
      Identifier.checkIdentifierSource(instName, "instance", path ++ List(instName))
      val id = InstanceIdentifier(instName)
      id -> InstanceSpec.fromYaml(body, path ++ List(instName), metaDef, id)
    }.toMap
  }

  def enumsFromYaml(src: yamlesque.Node, path: List[String]): Map[String, EnumSpec] = {
    val srcMap = ParseUtils.asMap(src, path)
    srcMap.obj.map { case (key, body) =>
      val enumName = ParseUtils.asStr(key, path)
      Identifier.checkIdentifierSource(enumName, "enum", path ++ List(enumName))
      enumName -> EnumSpec.fromYaml(body, path ++ List(enumName))
    }.toMap
  }

  def fromYaml(src: yamlesque.Node, fileName: Option[String]): ClassSpec = fromYaml(src, fileName, List(), MetaSpec.OPAQUE)

  def opaquePlaceholder(typeName: List[String]): ClassSpec = {
    val placeholder = ClassSpec(
      fileName = None,
      path = List(),
      isTopLevel = true,
      meta = MetaSpec.OPAQUE,
      doc = DocSpec.EMPTY,
      toStringExpr = None,
      params = List(),
      seq = List(),
      types = Map(),
      instances = Map(),
      enums = Map()
    )
    placeholder.name = typeName
    placeholder
  }
}
