package viper.gobra.translator.implementations.components

import viper.gobra.ast.internal.GlobalConst
import viper.gobra.ast.{internal => in}
import viper.gobra.translator.interfaces.{Collector, Context}
import viper.gobra.translator.interfaces.components.Fixpoint
import viper.silver.ast.{Exp, Type, TypeVar}
import viper.silver.{ast => vpr}

class FixpointImpl extends Fixpoint {

  /**
    * Finalizes translation. May add to collector.
    */
  override def finalize(col: Collector): Unit = {
    generatedDomains foreach col.addMember
  }

  override def create(gc: in.GlobalConstDecl)(ctx: Context): Unit = {
    val domainName = constantDomainName(gc.left)
    val (pos, info, errT) = gc.vprMeta

    val getFunc = constantGetDomainFunc(gc.left)(ctx)
    val getFuncApp = get(gc.left)(ctx)
    val getAxiom = vpr.NamedDomainAxiom(
      name = s"get_constant${gc.left.id}",
      exp = vpr.EqCmp(getFuncApp, ctx.expr.translate(gc.right)(ctx).res)(pos, info, errT),
    )(domainName = domainName)

    val domain = vpr.Domain(
      domainName,
      Seq(getFunc),
      Seq(getAxiom),
      Seq()
    )()
    _generatedDomains ::= domain
  }

  override def get(gc: in.GlobalConst)(ctx: Context): vpr.DomainFuncApp =
    vpr.DomainFuncApp(constantGetDomainFunc(gc)(ctx), Seq[Exp](), Map[TypeVar, Type]())()

  private def constantGetDomainFunc(gc: in.GlobalConst)(ctx: Context): vpr.DomainFunc = gc match {
    case v: in.GlobalConst.Val =>
      vpr.DomainFunc(
        name = s"constant_${v.id}",
        formalArgs = Seq(),
        typ = ctx.typ.translate(v.typ)(ctx)
      )(domainName = constantDomainName(v))
    case _ => ???
  }

  def generatedDomains: List[vpr.Domain] = _generatedDomains

  private var _generatedDomains: List[vpr.Domain] = List.empty

  private def constantDomainName(c: GlobalConst): String = s"Constant${c.id}"
}