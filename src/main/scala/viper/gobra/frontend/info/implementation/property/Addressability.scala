package viper.gobra.frontend.info.implementation.property

import viper.gobra.ast.frontend._
import viper.gobra.frontend.info.base.SymbolTable.{Field, Variable}
import viper.gobra.frontend.info.base.Type.{ArrayT, SliceT}
import viper.gobra.frontend.info.implementation.TypeInfoImpl

trait Addressability extends BaseProperty { this: TypeInfoImpl =>

  lazy val effAddressable: Property[PExpression] = createBinaryProperty("effective addressable") {
    case _: PCompositeLit => true
    case e => addressable(e)
  }

  // depends on: entity, tipe
  lazy val addressable: Property[PExpression] = createBinaryProperty("addressable") {
    case PNamedOperand(id) => entity(id).isInstanceOf[Variable]
    case _: PReference => true
    case PIndexedExp(b, _) => val bt = exprType(b); bt.isInstanceOf[SliceT] || (b.isInstanceOf[ArrayT] && addressable(b))
    case PSelection(b, id) => entity(id).isInstanceOf[Field] && addressable(b)
    case PSelectionOrMethodExpr(_, id) => entity(id).isInstanceOf[Field] // variables are always addressable
    case _ => false
  }
}