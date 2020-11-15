// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.gobra.translator.implementations.translator

import viper.gobra.ast.{internal => in}
import viper.gobra.translator.interfaces.translator.PureMethods
import viper.gobra.translator.interfaces.{Collector, Context}
import viper.silver.{ast => vpr}
import viper.gobra.reporting.Source.Parser
import viper.gobra.util.Violation
import viper.gobra.theory.Addressability.Exclusive
import viper.gobra.ast.internal.transform.OverflowChecksTransform

class PureMethodsImpl extends PureMethods {

  import viper.gobra.translator.util.ViperWriter._
  import MemberLevel._

  /**
    * Finalizes translation. May add to collector.
    */
  override def finalize(col: Collector): Unit = ()

  // todo fold

  private def encodeBlockToExpression(
      x: in.Block,
      args: Vector[in.Parameter.In],
      res: Vector[in.Parameter.Out]
  ): in.Expr = {
    sealed trait pstmt { def v: in.LocalVar }
    class cAssg(val v: in.LocalVar, val cnd: Vector[in.Expr], val newval: in.Expr, val oldval: in.Expr) extends pstmt
    class uAssg(val v: in.LocalVar, val newval: in.Expr) extends pstmt

    var vars: Map[String, in.Expr] = Map()
    def setVar(s: String, v: in.Expr) { vars += (s -> v) }
    def getVar(s: String): in.Expr = {
      if (vars.get(s) == Option.empty) {
        println("doesn't have s")
      }
      (vars get s).get
    }
    var returnVar: in.Expr = in.BoolLit(true)(Parser.Internal)

    var vartagCounter = 0
    def genVartag(s: String, typ: in.Type): in.LocalVar = {
      vartagCounter += 1
      in.LocalVar(s"localvar_$s" + s"_$vartagCounter", typ)(Parser.Internal)
    }
    def genReturnTag(): in.LocalVar = {
      vartagCounter += 1
      in.LocalVar(s"returnvar_$vartagCounter", in.BoolT(Exclusive))(Parser.Internal)
    }

    def neg(b: in.Expr): in.Expr = in.Negation(b)(Parser.Internal)
    def andConditions(c: Vector[in.Expr]): in.Expr = {
      if (c.isEmpty) {
        return in.BoolLit(true)(Parser.Internal)
      }
      c.reduce((a, b) => in.And(a, b)(Parser.Internal))
    }

    def goStmt(x: in.Stmt, path: Vector[in.Expr]): Vector[pstmt] =
      x match {
        case in.Block(decls, stmts) => {
          def f(b: in.BlockDeclaration): pstmt =
            b match {
              case in.LocalVar(id, typ) => {
                val vn = genVartag(id, typ)
                setVar(id, vn)
                new uAssg(vn, in.DfltVal(typ)(Parser.Internal))
              }
            }
          decls.map { f } ++ stmts.map(goStmt(_, path)).flatten
        }

        case in.Seqn(stmts) => {
          stmts.map(goStmt(_, path)).flatten
        }

        case in.If(cond, thn, els) => {
          val eCond = goExpr(cond)
          val eThn = goStmt(thn, path :+ eCond)
          val eEls = goStmt(els, path :+ neg(eCond))
          eThn ++ eEls
        }

        case ass @ in.SingleAss(assignee, expr) => {
          assignee match {
            //case in.Assignee.Var(v) => {
            case in.Assignee.Var(v: in.LocalVar) => {
              val eExpr = goExpr(expr)
              val oldVn = getVar(v.id)
              //val vn = genVartag(v.id, eExpr.typ)
              val vn = genVartag(v.id, v.typ)
              setVar(v.id, vn)
              Vector(new cAssg(vn, path :+ returnVar, eExpr, oldVn))
            }
            case in.Assignee.Var(v: in.Parameter.Out) => {
              val eExpr = goExpr(expr)
              val oldVn = getVar(v.id)
              //val vn = genVartag(v.id, eExpr.typ)
              val vn = genVartag(v.id, v.typ)
              setVar(v.id, vn)
              Vector(new cAssg(vn, path :+ returnVar, eExpr, oldVn))
            }
            case _ =>
              Violation.violation(s"Assignee '$assignee' in assignment '$ass' cannot be assigned in a pure function")
          }
        }

        case in.Return() => {
          val rt = genReturnTag()
          val oldRt = returnVar
          returnVar = rt
          Vector(new cAssg(rt, path, in.BoolLit(false)(Parser.Internal), oldRt))
        }
        // case fold: in.Fold =>
        // case unfold: in.Unfold =>
        // case in.While(cond, invs, body) =>
        // case in.FunctionCall(targets, func, args) =>
        // case in.MethodCall(targets, recv, meth, args) =>
        case in.Fold(_) | in.Unfold(_) | in.While(_, _, _) | in.FunctionCall(_, _, _) | in.MethodCall(_, _, _, _) =>
          Violation.violation(s"Statement $x not yet implemented.")
        // case in.Assert(ass) =>
        // case in.Assume(ass) =>
        // case in.Inhale(ass) =>
        // case in.Exhale(ass) =>
        case in.Assert(_) | in.Assume(_) | in.Inhale(_) | in.Exhale(_) =>
          Violation.violation(s"Statement $x not supported in pure function.")
        case _ => Violation.violation(s"Statement $x did not match with any implemented case.")
      }
    def goAccess(x: in.Access): in.Access =
      in.Access(x.e match {
        case in.Accessible.Address(op) => in.Accessible.Address(goExpr[in.Location](op))
        case in.Accessible.Predicate(op) =>
          in.Accessible.Predicate((op match {
            case in.FPredicateAccess(pred, args)       => in.FPredicateAccess(pred, args.map(goExpr)) _
            case in.MPredicateAccess(recv, pred, args) => in.MPredicateAccess(goExpr(recv), pred, args.map(goExpr)) _
            case in.MemoryPredicateAccess(arg)         => in.MemoryPredicateAccess(goExpr(arg)) _
          })(Parser.Internal))
      })(Parser.Internal)
    def goExpr[E <: in.Expr](x: E): E = {
      println("####", x, x.getClass())
      val result = x match {
        case in.LessCmp(l, r)               => in.LessCmp(goExpr(l), goExpr(r))(Parser.Internal)
        case in.AtMostCmp(l, r)             => in.AtMostCmp(goExpr(l), goExpr(r))(Parser.Internal)
        case in.GreaterCmp(l, r)            => in.GreaterCmp(goExpr(l), goExpr(r))(Parser.Internal)
        case in.AtLeastCmp(l, r)            => in.AtLeastCmp(goExpr(l), goExpr(r))(Parser.Internal)
        case in.EqCmp(l, r)                 => in.EqCmp(goExpr(l), goExpr(r))(Parser.Internal)
        case in.UneqCmp(l, r)               => in.UneqCmp(goExpr(l), goExpr(r))(Parser.Internal)
        case in.Negation(b)                 => in.Negation(goExpr(b))(Parser.Internal)
        case in.And(l, r)                   => in.And(goExpr(l), goExpr(r))(Parser.Internal)
        case in.Or(l, r)                    => in.Or(goExpr(l), goExpr(r))(Parser.Internal)
        case in.Add(l, r)                   => in.Add(goExpr(l), goExpr(r))(Parser.Internal)
        case in.Sub(l, r)                   => in.Sub(goExpr(l), goExpr(r))(Parser.Internal)
        case in.Mul(l, r)                   => in.Mul(goExpr(l), goExpr(r))(Parser.Internal)
        case in.Div(l, r)                   => in.Div(goExpr(l), goExpr(r))(Parser.Internal)
        case in.Mod(l, r)                   => in.Mod(goExpr(l), goExpr(r))(Parser.Internal)
        case in.Cardinality(exp)            => in.Cardinality(goExpr(exp))(Parser.Internal)
        case in.Contains(left, right)       => in.Contains(goExpr(left), goExpr(right))(Parser.Internal)
        case in.Intersection(left, right)   => in.Intersection(goExpr(left), goExpr(right))(Parser.Internal)
        case in.Length(exp)                 => in.Length(goExpr(exp))(Parser.Internal)
        case in.Multiplicity(left, right)   => in.Multiplicity(goExpr(left), goExpr(right))(Parser.Internal)
        case in.MultisetConversion(expr)    => in.MultisetConversion(goExpr(expr))(Parser.Internal)
        case in.OptionGet(exp)              => in.OptionGet(goExpr(exp))(Parser.Internal)
        case n: in.OptionNone               => n
        case in.OptionSome(exp)             => in.OptionSome(goExpr(exp))(Parser.Internal)
        case in.RangeSequence(low, high)    => in.RangeSequence(goExpr(low), goExpr(high))(Parser.Internal)
        case in.SequenceAppend(left, right) => in.SequenceAppend(goExpr(left), goExpr(right))(Parser.Internal)
        case in.SequenceConversion(expr)    => in.SequenceConversion(goExpr(expr))(Parser.Internal)
        case in.SequenceDrop(left, right)   => in.SequenceDrop(goExpr(left), goExpr(right))(Parser.Internal)
        case in.SequenceTake(left, right)   => in.SequenceTake(goExpr(left), goExpr(right))(Parser.Internal)
        case in.SetConversion(expr)         => in.SetConversion(goExpr(expr))(Parser.Internal)
        case in.SetMinus(left, right)       => in.SetMinus(goExpr(left), goExpr(right))(Parser.Internal)
        case in.Subset(left, right)         => in.Subset(goExpr(left), goExpr(right))(Parser.Internal)
        case in.Union(left, right) =>
          in.Union(goExpr(left), goExpr(right))(Parser.Internal)
        case in.ArrayUpdate(base, left, right) =>
          in.ArrayUpdate(goExpr(base), goExpr(left), goExpr(right))(Parser.Internal)
        case in.SequenceUpdate(base, left, right) =>
          in.SequenceUpdate(goExpr(base), goExpr(left), goExpr(right))(Parser.Internal)
        case in.StructUpdate(base, field, newVal) =>
          in.StructUpdate(goExpr(base), field, goExpr(newVal))(Parser.Internal)
        case l: in.BoolLit                     => l
        case l: in.IntLit                      => l
        case l: in.NilLit                      => l
        case in.ArrayLit(memberType, exprs)    => in.ArrayLit(memberType, exprs.map(goExpr))(Parser.Internal)
        case in.MultisetLit(memberType, exprs) => in.MultisetLit(memberType, exprs.map(goExpr))(Parser.Internal)
        case in.SequenceLit(memberType, exprs) => in.SequenceLit(memberType, exprs.map(goExpr))(Parser.Internal)
        case in.SetLit(memberType, exprs)      => in.SetLit(memberType, exprs.map(goExpr))(Parser.Internal)
        case in.StructLit(typ, args)           => in.StructLit(typ, args.map(goExpr))(Parser.Internal)

        case d: in.DfltVal                    => d
        case v: in.GlobalConst.Val            => v
        case in.Ref(in.Addressable.Var(v), _) => in.Ref(v)(Parser.Internal) // Todo does this even make sense
        case in.Ref(in.Addressable.Index(in.IndexedExp(base, index)), _) =>
          in.Ref(in.IndexedExp(goExpr(base), goExpr(index))(Parser.Internal))(Parser.Internal)
        case in.Ref(in.Addressable.Field(in.FieldRef(recv, field)), _) =>
          in.Ref(in.FieldRef(goExpr(recv), field)(Parser.Internal))(Parser.Internal)
        case in.Ref(in.Addressable.Pointer(in.Deref(exp, ptyp)), _) =>
          in.Ref(in.Deref(goExpr(exp), ptyp)(Parser.Internal))(Parser.Internal)
        case in.Tuple(x) => in.Tuple(x.map(goExpr))(Parser.Internal)

        case in.LetIn(in.SingleAss(left, right), expr, typ) =>
          in.LetIn(in.SingleAss(left, goExpr(right))(Parser.Internal), goExpr(expr), typ)(
            Parser.Internal
          ) // Todo make newly created variable to be renamed

        case in.Conditional(cond, thn, els, typ) =>
          in.Conditional(goExpr(cond), goExpr(thn), goExpr(els), typ)(Parser.Internal)

        case u @ in.Unfolding(acc, in) => u.copy(goAccess(acc), goExpr(in))(Parser.Internal)

        case in.LocalVar(id, typ)       => getVar(id)
        case in.IndexedExp(base, index) => in.IndexedExp(goExpr(base), goExpr(index))(Parser.Internal)
        case in.FieldRef(recv, field)   => in.FieldRef(goExpr(recv), field)(Parser.Internal)
        case in.Deref(exp, typ)         => in.Deref(goExpr(exp), typ)(Parser.Internal)
        case i: in.Parameter.In         => i
        case o: in.Parameter.Out        => o

        case in.PureFunctionCall(func, args, typ) =>
          in.PureFunctionCall(func, args.map(goExpr), typ)(Parser.Internal)

        case in.PureMethodCall(recv, meth, args, typ) =>
          in.PureMethodCall(goExpr(recv), meth, args.map(goExpr), typ)(Parser.Internal)

        case in.Old(_, _) | in.PureForall(_, _, _) | in.Exists(_, _, _) | in.BoundVar(_, _) =>
          Violation.violation(s"Expression $x not supported in expression in pure function")
        //case _ => Violation.violation(s"Expression $x ${x.getClass()} did not match with any implemented case.")
      }
      result.asInstanceOf[E]
    }
    def encodePstmt(stmt: pstmt, e: in.Expr): in.Expr = {
      val ex = stmt match {
        case u: uAssg => u.newval
        case c: cAssg => in.Conditional(andConditions(c.cnd), c.newval, c.oldval, c.newval.typ)(Parser.Internal)
      }
      in.LetIn(in.SingleAss(in.Assignee(stmt.v), ex)(Parser.Internal), e, e.typ)(Parser.Internal)
    }
    def optimizePstmt(stmt: pstmt): pstmt =
      stmt match {
        case u: uAssg => u
        case c: cAssg => {
          if (c.cnd == Vector(in.BoolLit(true)(Parser.Internal)) || c.cnd == Vector()) {
            println("optimizing true path condition", c)
            return new uAssg(c.v, c.newval)
          }
          println("unoptimized path condition", c.v, c.cnd, c.newval, c.oldval)
          c
        }
      }
    args.foreach(a => setVar(a.id, a))
    res.foreach(a => setVar(a.id, in.DfltVal(a.typ)(Parser.Internal)))

    val pstmts = goStmt(x, Vector())
    println("##########")
    pstmts.foreach(_ match {
      case u: uAssg => println("uAssg", u.v, u.newval)
      case c: cAssg => println("cassg", c.v, c.cnd, c.newval, c.oldval)
    })
    println("##########")
    val opstmts = pstmts.map(optimizePstmt)
    println("return id", res.head.id)
    println("variable", getVar(res.head.id))
    println("type", getVar(res.head.id).typ)
    opstmts.foldRight[in.Expr](getVar(res.head.id))(encodePstmt(_, _))
    //(getVar(res.head.id))
  }

  override def pureMethod(meth: in.PureMethod)(ctx: Context): MemberWriter[vpr.Function] = {
    require(meth.results.size == 1)

    val (pos, info, errT) = meth.vprMeta

    val vRecv = ctx.typeEncoding.variable(ctx)(meth.receiver)
    val vRecvPres = ctx.typeEncoding.precondition(ctx).lift(meth.receiver).toVector

    val vArgs = meth.args.map(ctx.typeEncoding.variable(ctx))
    val vArgPres = meth.args.flatMap(ctx.typeEncoding.precondition(ctx).lift(_))

    val vResults = meth.results.map(ctx.typeEncoding.variable(ctx))
    val vResultPosts = meth.results.flatMap(ctx.typeEncoding.postcondition(ctx).lift(_))
    assert(vResults.size == 1)
    val resultType = if (vResults.size == 1) vResults.head.typ else ctx.tuple.typ(vResults map (_.typ))

    val fixResultvar = (x: vpr.Exp) => {
      x.transform { case v: vpr.LocalVar if v.name == meth.results.head => vpr.Result(resultType)() }
    }

    val transformed = meth.body.map(encodeBlockToExpression(_, meth.args :+ meth.receiver, meth.results))
    // val overflowPosts =
    //   transformed.map(OverflowChecksTransform.getPureBlockPosts(_, meth.results)).getOrElse((Vector()))
    // val vOverflowPosts = overflowPosts.map(ctx.ass.postcondition(_)(ctx))

    for {
      pres <- sequence((vRecvPres ++ vArgPres) ++ meth.pres.map(ctx.ass.precondition(_)(ctx)))
      posts <- sequence(
        //vResultPosts ++ vOverflowPosts ++ meth.posts.map(ctx.ass.postcondition(_)(ctx).map(fixResultvar(_)))
        vResultPosts ++ meth.posts.map(ctx.ass.postcondition(_)(ctx).map(fixResultvar(_)))
      )

      body <- option(transformed map { b =>
        pure(
          for {
            results <- ctx.expr.translate(b)(ctx)
          } yield results
        )(ctx)
      })

      function = vpr.Function(
        name = meth.name.uniqueName,
        formalArgs = vRecv +: vArgs,
        typ = resultType,
        pres = pres,
        posts = posts,
        body = body
      )(pos, info, errT)

    } yield function
  }

  override def pureFunction(func: in.PureFunction)(ctx: Context): MemberWriter[vpr.Function] = {
    require(func.results.size == 1)

    val (pos, info, errT) = func.vprMeta

    val vArgs = func.args.map(ctx.typeEncoding.variable(ctx))
    val vArgPres = func.args.flatMap(ctx.typeEncoding.precondition(ctx).lift(_))

    val vResults = func.results.map(ctx.typeEncoding.variable(ctx))
    val vResultPosts = func.results.flatMap(ctx.typeEncoding.postcondition(ctx).lift(_))
    assert(vResults.size == 1)
    val resultType = if (vResults.size == 1) vResults.head.typ else ctx.tuple.typ(vResults map (_.typ))

    val fixResultvar = (x: vpr.Exp) => {
      x.transform { case v: vpr.LocalVar if v.name == func.results.head.id => vpr.Result(resultType)() }
    }

    val transformed = func.body.map(encodeBlockToExpression(_, func.args, func.results))
    val overflowPosts =
      transformed.map(OverflowChecksTransform.getPureBlockPosts(_, func.results)).getOrElse((Vector()))
    val vOverflowPosts = overflowPosts.map(ctx.ass.postcondition(_)(ctx))

    for {
      pres <- sequence(vArgPres ++ func.pres.map(ctx.ass.precondition(_)(ctx)))
      posts <- sequence(
        vResultPosts ++ vOverflowPosts ++ func.posts.map(ctx.ass.postcondition(_)(ctx).map(fixResultvar(_)))
        // vResultPosts ++ func.posts.map(ctx.ass.postcondition(_)(ctx).map(fixResultvar(_)))
      )

      body <- option(transformed map { b =>
        // body <- option(func.body map { b =>
        pure(
          for {
            results <- ctx.expr.translate(b)(ctx)
            // results <- ctx.expr.translate(encodeBlockToExpression(b, func.args, func.results))(ctx)
          } yield results
        )(ctx)
      })

      function = vpr.Function(
        name = func.name.name,
        formalArgs = vArgs,
        typ = resultType,
        pres = pres,
        posts = posts,
        body = body
      )(pos, info, errT)

    } yield function
  }

}
