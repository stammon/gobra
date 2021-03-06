// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.gobra.translator.encodings.arrays

import viper.gobra.translator.encodings.EmbeddingComponent
import viper.gobra.translator.interfaces.{Collector, Context}
import viper.gobra.ast.{internal => in}
import viper.silver.{ast => vpr}
import ArrayEncoding.ComponentParameter
import viper.gobra.reporting.Source
import viper.gobra.theory.Addressability.{Exclusive, Shared}
import viper.gobra.translator.{Names, encodings}
import viper.gobra.translator.interfaces.translator.Generator
import viper.gobra.translator.util.FunctionGenerator
import viper.gobra.translator.util.ViperWriter.CodeLevel.pure


class SharedArrayComponentImpl extends SharedArrayComponent {

  override def finalize(col: Collector): Unit = {
    array.finalize(col)
    emb.finalize(col)
    arrayNilFunc.finalize(col)
  }

  private val array: ParameterizedArrayDomain = new ParameterizedArrayDomain

  /**
    * Generates:
    * function arrayNil(): Array[ [T@] ]
    *   ensures len(result) == 1 && Forall idx :: {array_get(result, idx)} array_get(result, idx) == [dflt(T@)]
    * */
  private val arrayNilFunc: FunctionGenerator[ComponentParameter] = new FunctionGenerator[(BigInt, in.Type)]{
    def genFunction(t: (BigInt, in.Type))(ctx: Context): vpr.Function = {
      val vResType = array.typ(ctx.typeEncoding.typ(ctx)(t._2))
      val src = in.DfltVal(in.ArrayT(t._1, t._2, Shared))(Source.Parser.Internal)
      val idx = in.BoundVar("idx", in.IntT(Exclusive))(src.info)
      val vIdx = ctx.typeEncoding.variable(ctx)(idx)
      val resAccess = array.loc(vpr.Result(vResType)(), vIdx.localVar)()
      val idxEq = vpr.EqCmp(resAccess, pure(ctx.expr.translate(in.DfltVal(t._2)(src.info))(ctx))(ctx).res)()
      val forall = vpr.Forall(
        Seq(vIdx),
        Seq(vpr.Trigger(Seq(resAccess))()),
        idxEq
      )()


      vpr.Function(
        name = s"${Names.arrayDefaultFunc}_${Names.freshName}",
        formalArgs = Seq.empty,
        typ = vResType,
        pres = Seq.empty,
        posts = Vector(vpr.EqCmp(array.len(vpr.Result(vResType)())(), vpr.IntLit(1)())(), forall),
        body = None
      )()
    }
  }

  /** Embeds Arrays of fixed length as specified by ComponentParameter. */
  private val emb: EmbeddingComponent[ComponentParameter] = new encodings.EmbeddingComponent.Impl[ComponentParameter](
    p = (e: vpr.Exp, id: ComponentParameter) => (ctx: Context) =>
      vpr.Or( // len(a) == n || a == arrayNil
        vpr.EqCmp(array.len(e)(), vpr.IntLit(id._1)())(),
        vpr.EqCmp(e, arrayNilFunc(Vector.empty, id)()(ctx))()
      )(),
    t = (id: ComponentParameter) => (ctx: Context) => array.typ(ctx.typeEncoding.typ(ctx)(id._2))
  )

  /** Returns type of exclusive-array domain. */
  override def typ(t: ComponentParameter)(ctx: Context): vpr.Type = emb.typ(t)(ctx)

  /** Getter of shared-array domain. */
  override def get(base: vpr.Exp, idx: vpr.Exp, t: ComponentParameter)(src: in.Node)(ctx: Context): vpr.Exp = {
    val (pos, info, errT) = src.vprMeta
    array.loc(emb.unbox(base, t)(pos, info, errT)(ctx), idx)(pos, info, errT) // unbox(base)[idx]
  }

  /** Nil of shared-struct domain */
  override def nil(t: ComponentParameter)(src: in.Node)(ctx: Context): vpr.Exp = {
    val (pos, info, errT) = src.vprMeta
    emb.box(arrayNilFunc(Vector.empty, t)(pos, info, errT)(ctx), t)(pos, info, errT)(ctx) // box(arrayNil())
  }


  /** Length of shared-array domain. */
  override def length(arg: vpr.Exp, t: ComponentParameter)(src: in.Node)(ctx: Context): vpr.Exp = {
    val (pos, info, errT) = src.vprMeta
    array.len(emb.unbox(arg, t)(pos, info, errT)(ctx))(pos, info, errT) // len(unbox(arg))
  }


  /** A specialized version of the array domain, where the element type is a parameter. */
  private class ParameterizedArrayDomain extends Generator {

    override def finalize(col: Collector): Unit = {
      if (generated) {
        col.addMember(domain)
      }
    }

    var generated: Boolean = false
    lazy val (domain, locFunc, lenFunc) = genDomain

    /** Returns the type of the array domain. */
    def typ(t: vpr.Type): vpr.Type = vpr.DomainType(domain, Map(vpr.TypeVar("T") -> t))

    /** Getter for the array domain. */
    def loc(a: vpr.Exp, i: vpr.Exp)(pos: vpr.Position = vpr.NoPosition, info: vpr.Info = vpr.NoInfo, errT: vpr.ErrorTrafo = vpr.NoTrafos): vpr.Exp = {
      vpr.DomainFuncApp(locFunc, Seq(a, i), a.typ.asInstanceOf[vpr.DomainType].typVarsMap)(pos, info, errT)
    }

    /** Length for the array domain. */
    def len(a: vpr.Exp)(pos: vpr.Position = vpr.NoPosition, info: vpr.Info = vpr.NoInfo, errT: vpr.ErrorTrafo = vpr.NoTrafos): vpr.Exp = {
      vpr.DomainFuncApp(lenFunc, Seq(a), a.typ.asInstanceOf[vpr.DomainType].typVarsMap)(pos, info, errT)
    }

    /**
      * Returns domain, loc function, and len function.
      *
      * Generates:
      * domain SharedArray[T] {
      *   function loc(a: SharedArray, i: Int): T
      *   function len(a: SharedArray): Int
      *   function first(r: T): SharedArray
      *   function second(r: T): Int
      *
      *   axiom {
      *     forall a: SharedArray, i: Int :: {loc(a, i)} 0 <= i && i < len(a) ==> first(loc(a, i)) == a && second(loc(a, i)) == i
      *   }
      *
      *   axiom {
      *     forall a: SharedArray :: {len(a)} len(a) >= 0
      *   }
      * }
      * */
    private def genDomain: (vpr.Domain, vpr.DomainFunc, vpr.DomainFunc) = {
      val domainName = Names.sharedArrayDomain
      val typeVar = vpr.TypeVar("T")
      val typeVarMap = Map(typeVar -> typeVar)
      val domainType = vpr.DomainType(domainName = domainName, typeVarMap)(Seq(typeVar))

      val aDecl = vpr.LocalVarDecl("a", domainType)()
      val a = aDecl.localVar
      val rDecl = vpr.LocalVarDecl("r", typeVar)()
      val iDecl = vpr.LocalVarDecl("i", vpr.Int)()
      val i = iDecl.localVar

      val locFunc = vpr.DomainFunc(s"${Names.sharedArrayDomain}loc", Seq(aDecl, iDecl), typeVar)(domainName = domainName)
      val lenFunc = vpr.DomainFunc(s"${Names.sharedArrayDomain}len", Seq(aDecl), vpr.Int)(domainName = domainName)
      val firstFunc = vpr.DomainFunc(s"${Names.sharedArrayDomain}first", Seq(rDecl), domainType)(domainName = domainName)
      val secondFunc = vpr.DomainFunc(s"${Names.sharedArrayDomain}second", Seq(rDecl), vpr.Int)(domainName = domainName)

      val locFuncApp = vpr.DomainFuncApp(locFunc, Seq(a, i), typeVarMap)()
      val lenFuncApp = vpr.DomainFuncApp(lenFunc, Seq(a), typeVarMap)()

      val injectivity = vpr.AnonymousDomainAxiom(
        vpr.Forall(
          Seq(aDecl, iDecl),
          Seq(vpr.Trigger(Seq(locFuncApp))()),
          vpr.Implies(
            vpr.And(
              vpr.LeCmp(vpr.IntLit(0)(), i)(),
              vpr.LtCmp(i, lenFuncApp)()
            )(),
            vpr.And(
              vpr.EqCmp(vpr.DomainFuncApp(firstFunc, Seq(locFuncApp), typeVarMap)(), a)(),
              vpr.EqCmp(vpr.DomainFuncApp(secondFunc, Seq(locFuncApp), typeVarMap)(), i)()
            )()
          )()
        )()
      )(domainName = domainName)

      val lenNonNeg = vpr.AnonymousDomainAxiom{
        vpr.Forall(
          Seq(aDecl),
          Seq(vpr.Trigger(Seq(lenFuncApp))()),
          vpr.GeCmp(lenFuncApp, vpr.IntLit(0)())()
        )()
      }(domainName = domainName)

      val domain = vpr.Domain(
        name = domainName,
        typVars = Seq(typeVar),
        functions = Seq(locFunc, lenFunc, firstFunc, secondFunc),
        axioms = Seq(injectivity, lenNonNeg)
      )()

      generated = true

      (domain, locFunc, lenFunc)
    }

  }

}
