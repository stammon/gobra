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
import viper.gobra.util.Violation
import viper.gobra.theory.Addressability.Exclusive
// import viper.gobra.ast.internal.transform.OverflowChecksTransform

class PureMethodsImpl extends PureMethods {

  import viper.gobra.translator.util.ViperWriter._
  import MemberLevel._

  /**
    * Finalizes translation. May add to collector.
    */
  override def finalize(col: Collector): Unit = ()

  private def encodeBlockToExpression(
      x: in.Block,
      args: Vector[in.Parameter.In],
      res: Vector[in.Parameter.Out]
  ): in.Expr = {
    sealed trait pstmt { def v: in.LocalVar }
    class cAssg(val v: in.LocalVar, val cnd: Vector[in.Expr], val newval: in.Expr, val oldval: in.Expr) extends pstmt
    class uAssg(val v: in.LocalVar, val newval: in.Expr) extends pstmt

    val finfo = x.info

    var vars: Map[String, in.Expr] = Map()
    var predFolding: Map[in.PredicateAccess, in.Expr] = Map()
    var returnVar: in.Expr = in.BoolLit(true)(finfo)
    def setVar(s: String, v: in.Expr) = vars += (s -> v)
    def getVar(s: String): in.Expr = (vars get s).get

    var vartagCounter = 0
    def genVartag(s: String, typ: in.Type): in.LocalVar = {
      vartagCounter += 1
      in.LocalVar(s"localvar_$s" + s"_$vartagCounter", typ)(finfo)
    }
    def genReturnTag(): in.LocalVar = {
      vartagCounter += 1
      in.LocalVar(s"returnvar_$vartagCounter", in.BoolT(Exclusive))(finfo)
    }

    def neg(b: in.Expr): in.Expr = in.Negation(b)(finfo)
    def andConditions(c: Vector[in.Expr]): in.Expr = {
      if (c.isEmpty) {
        return in.BoolLit(true)(finfo)
      }
      c.reduce((a, b) => in.And(a, b)(finfo))
    }


    def computePath(p:Vector[in.Expr]):Vector[in.Expr] = returnVar +: p

    def goStmt(x: in.Stmt, path: Vector[in.Expr]): Vector[pstmt] =
      x match {
        case in.Block(decls, stmts) => {
          def f(b: in.BlockDeclaration): pstmt =
            b match {  // todo do declarations even need to be assigned a default value? or is it handled by the desugarer?
              case in.LocalVar(id, typ) => {
                val vn = genVartag(id, typ)
                setVar(id, vn)
                new uAssg(vn, in.DfltVal(typ)(finfo))
              }
            }
          decls.map { f } ++ stmts.map(goStmt(_, path)).flatten
        }

        case in.Seqn(stmts) => {
          stmts.map(goStmt(_, path)).flatten
        }

        case in.If(cond, thn, els) => {
          val eCond = goE(cond)
          val eThn = goStmt(thn, path :+ eCond)
          val eEls = goStmt(els, path :+ neg(eCond))
          eThn ++ eEls
        }

        case ass @ in.SingleAss(assignee, expr) => {
          assignee match {
            //case in.Assignee.Var(v) => {
            case in.Assignee.Var(v: in.LocalVar) => {
              val eExpr = goE(expr)
              val oldVn = getVar(v.id)
              //val vn = genVartag(v.id, eExpr.typ)
              val vn = genVartag(v.id, v.typ)
              setVar(v.id, vn)
              Vector(new cAssg(vn, computePath(path), eExpr, oldVn))
            }
            case in.Assignee.Var(v: in.Parameter.Out) => {
              val eExpr = goE(expr)
              val oldVn = getVar(v.id)
              //val vn = genVartag(v.id, eExpr.typ)
              val vn = genVartag(v.id, v.typ)
              setVar(v.id, vn)
              Vector(new cAssg(vn, computePath(path), eExpr, oldVn))
            }
            case _ =>
              Violation.violation(s"Assignee '$assignee' in assignment '$ass' cannot be assigned in a pure function")
          }
        }

        case in.Return() => {
          val rt = genReturnTag()
          val oldRt = returnVar
          val cassg = new cAssg(rt, computePath(path), in.BoolLit(false)(finfo), oldRt)
          returnVar = rt
          Vector(cassg)
        }
        case in.Unfold(utacc) => {
          val acc = goAccess(utacc) // todo goAccess could not work since we didn't cover it in Unfoldin in
          acc.e match {
            case in.Accessible.Predicate(op) => {
              println("unfold",op,predFolding.contains(op),predFolding.get(op))
              println("predfolding",predFolding)
              if(predFolding.contains(op)){
                // todo assert predicate not already unfolded
                predFolding+=(op-> in.Conditional(
                  andConditions(computePath(path)),
                  in.BoolLit(true)(finfo),
                  predFolding.get(op).get,
                  in.BoolT(Exclusive)
                )(finfo))
              } else {
                predFolding+=(op->andConditions(computePath(path)))
              }
            }
            case in.Accessible.Address(op) => Violation.violation("Unfold don't take address")
          }
          Vector()
        }
        case in.Fold(utacc) => {
          val acc = goAccess(utacc) // todo goAccess could not work since we didn't cover it in Unfoldin in
          acc.e match {
            case in.Accessible.Predicate(op) => {
              println("fold",op,predFolding.contains(op),predFolding.get(op))
              println("predfolding",predFolding)
              if(predFolding.contains(op)){
                // todo assert predicate unfolded
                // todo assert all predicates are folded back in the end?
                predFolding+=(op-> in.Conditional(
                  andConditions(computePath(path)),
                  in.BoolLit(false)(finfo),
                  predFolding.get(op).get,
                  in.BoolT(Exclusive)
                )(finfo))
              } else {
                predFolding+=(op->neg(andConditions(computePath(path))))
              }
            }
            case in.Accessible.Address(op) => Violation.violation("Fold don't take address")
          }
          Vector()
        }
        
        // case in.While(cond, invs, body) =>
        // case in.FunctionCall(targets, func, args) =>
        // case in.MethodCall(targets, recv, meth, args) =>
        case in.While(_, _, _) | in.FunctionCall(_, _, _) | in.MethodCall(_, _, _, _) =>
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
        case y @ in.Accessible.Predicate(op) =>
          in.Accessible.Predicate((op match {
            case in.FPredicateAccess(pred, args)       => in.FPredicateAccess(pred, args.map(goExpr)) _
            case in.MPredicateAccess(recv, pred, args) => in.MPredicateAccess(goExpr(recv), pred, args.map(goExpr)) _
            case in.MemoryPredicateAccess(arg)         => in.MemoryPredicateAccess(goExpr(arg)) _
          })(y.info))
      })(x.info)
    def goE(x:in.Expr):in.Expr = {
      predFolding.foldLeft(goExpr(x))((exp,pair)=>{
        val (pred,isfolded) = pair
        in.Conditional(
          isfolded ,
          in.Unfolding(in.Access(in.Accessible.Predicate(pred))(finfo),exp)(finfo),
          exp,
          exp.typ
          )(finfo)
      })
    }
    def goExpr[E <: in.Expr](x: E): E = {
      println("####", x, x.getClass())
      val result = x match {
        case y @ in.LessCmp(l, r)               => in.LessCmp(goExpr(l), goExpr(r))(y.info)
        case y @ in.AtMostCmp(l, r)             => in.AtMostCmp(goExpr(l), goExpr(r))(y.info)
        case y @ in.GreaterCmp(l, r)            => in.GreaterCmp(goExpr(l), goExpr(r))(y.info)
        case y @ in.AtLeastCmp(l, r)            => in.AtLeastCmp(goExpr(l), goExpr(r))(y.info)
        case y @ in.EqCmp(l, r)                 => in.EqCmp(goExpr(l), goExpr(r))(y.info)
        case y @ in.UneqCmp(l, r)               => in.UneqCmp(goExpr(l), goExpr(r))(y.info)
        case y @ in.Negation(b)                 => in.Negation(goExpr(b))(y.info)
        case y @ in.And(l, r)                   => in.And(goExpr(l), goExpr(r))(y.info)
        case y @ in.Or(l, r)                    => in.Or(goExpr(l), goExpr(r))(y.info)
        case y @ in.Add(l, r)                   => in.Add(goExpr(l), goExpr(r))(y.info)
        case y @ in.Sub(l, r)                   => in.Sub(goExpr(l), goExpr(r))(y.info)
        case y @ in.Mul(l, r)                   => in.Mul(goExpr(l), goExpr(r))(y.info)
        case y @ in.Div(l, r)                   => in.Div(goExpr(l), goExpr(r))(y.info)
        case y @ in.Mod(l, r)                   => in.Mod(goExpr(l), goExpr(r))(y.info)
        case y @ in.Cardinality(exp)            => in.Cardinality(goExpr(exp))(y.info)
        case y @ in.Contains(left, right)       => in.Contains(goExpr(left), goExpr(right))(y.info)
        case y @ in.Intersection(left, right)   => in.Intersection(goExpr(left), goExpr(right))(y.info)
        case y @ in.Length(exp)                 => in.Length(goExpr(exp))(y.info)
        case y @ in.Multiplicity(left, right)   => in.Multiplicity(goExpr(left), goExpr(right))(y.info)
        case y @ in.MultisetConversion(expr)    => in.MultisetConversion(goExpr(expr))(y.info)
        case y @ in.OptionGet(exp)              => in.OptionGet(goExpr(exp))(y.info)
        case n: in.OptionNone               => n
        case y @ in.OptionSome(exp)             => in.OptionSome(goExpr(exp))(y.info)
        case y @ in.RangeSequence(low, high)    => in.RangeSequence(goExpr(low), goExpr(high))(y.info)
        case y @ in.SequenceAppend(left, right) => in.SequenceAppend(goExpr(left), goExpr(right))(y.info)
        case y @ in.SequenceConversion(expr)    => in.SequenceConversion(goExpr(expr))(y.info)
        case y @ in.SequenceDrop(left, right)   => in.SequenceDrop(goExpr(left), goExpr(right))(y.info)
        case y @ in.SequenceTake(left, right)   => in.SequenceTake(goExpr(left), goExpr(right))(y.info)
        case y @ in.SetConversion(expr)         => in.SetConversion(goExpr(expr))(y.info)
        case y @ in.SetMinus(left, right)       => in.SetMinus(goExpr(left), goExpr(right))(y.info)
        case y @ in.Subset(left, right)         => in.Subset(goExpr(left), goExpr(right))(y.info)
        case y @ in.Union(left, right) =>
          in.Union(goExpr(left), goExpr(right))(y.info)
        case y @ in.ArrayUpdate(base, left, right) =>
          in.ArrayUpdate(goExpr(base), goExpr(left), goExpr(right))(y.info)
        case y @ in.SequenceUpdate(base, left, right) =>
          in.SequenceUpdate(goExpr(base), goExpr(left), goExpr(right))(y.info)
        case y @ in.StructUpdate(base, field, newVal) =>
          in.StructUpdate(goExpr(base), field, goExpr(newVal))(y.info)
        case l: in.BoolLit                     => l
        case l: in.IntLit                      => l
        case l: in.NilLit                      => l
        case y @ in.ArrayLit(memberType, exprs)    => in.ArrayLit(memberType, exprs.map(goExpr))(y.info)
        case y @ in.MultisetLit(memberType, exprs) => in.MultisetLit(memberType, exprs.map(goExpr))(y.info)
        case y @ in.SequenceLit(memberType, exprs) => in.SequenceLit(memberType, exprs.map(goExpr))(y.info)
        case y @ in.SetLit(memberType, exprs)      => in.SetLit(memberType, exprs.map(goExpr))(y.info)
        case y @ in.StructLit(typ, args)           => in.StructLit(typ, args.map(goExpr))(y.info)

        case d: in.DfltVal                    => d
        case v: in.GlobalConst.Val            => v
        case y @ in.Ref(in.Addressable.Var(v), _) => in.Ref(v)(y.info) // Todo does this even make sense
        case y @ in.Ref(in.Addressable.Index( idxExp @ in.IndexedExp(base, index)), _) =>
          in.Ref(in.IndexedExp(goExpr(base), goExpr(index))(idxExp.info))(y.info)
        case y @ in.Ref(in.Addressable.Field(frExp @ in.FieldRef(recv, field)), _) =>
          in.Ref(in.FieldRef(goExpr(recv), field)(frExp.info))(y.info)
        case y @ in.Ref(in.Addressable.Pointer(drExp @ in.Deref(exp, ptyp)), _) =>
          in.Ref(in.Deref(goExpr(exp), ptyp)(drExp.info))(y.info)
        case y @ in.Tuple(x) => in.Tuple(x.map(goExpr))(y.info)

        case y @ in.LetIn(assg @ in.SingleAss(left, right), expr, typ) =>
          in.LetIn(in.SingleAss(left, goExpr(right))(assg.info), goExpr(expr), typ)(
y.info
          ) // Todo make newly created variable to be checked, that it's name doesn't already exist

        case y @ in.Conditional(cond, thn, els, typ) =>
          in.Conditional(goExpr(cond), goExpr(thn), goExpr(els), typ)(y.info)

        case u @ in.Unfolding(acc, in) => u.copy(goAccess(acc), goExpr(in))(u.info)

        case in.LocalVar(id, typ)       => getVar(id)
        case y @ in.IndexedExp(base, index) => in.IndexedExp(goExpr(base), goExpr(index))(y.info)
        case y @ in.FieldRef(recv, field)   => in.FieldRef(goExpr(recv), field)(y.info)
        case y @ in.Deref(exp, typ)         => in.Deref(goExpr(exp), typ)(y.info)
        case i: in.Parameter.In         => i
        case o: in.Parameter.Out        => o

        case y @ in.PureFunctionCall(func, args, typ) =>
          in.PureFunctionCall(func, args.map(goExpr), typ)(y.info)

        case y @ in.PureMethodCall(recv, meth, args, typ) =>
          in.PureMethodCall(goExpr(recv), meth, args.map(goExpr), typ)(y.info)

        case in.Old(_, _) | in.PureForall(_, _, _) | in.Exists(_, _, _) | in.BoundVar(_, _) =>
          Violation.violation(s"Expression $x not supported in expression in pure function")
        //case _ => Violation.violation(s"Expression $x ${x.getClass()} did not match with any implemented case.")
      }
      result.asInstanceOf[E]
    }
    def encodePstmt(stmt: pstmt, e: in.Expr): in.Expr = {
      val ex = stmt match {
        case u: uAssg => u.newval
        case c: cAssg => in.Conditional(andConditions(c.cnd), c.newval, c.oldval, c.newval.typ)(finfo)
      }
      in.LetIn(in.SingleAss(in.Assignee(stmt.v), ex)(finfo), e, e.typ)(finfo)
    }
    def optimizePstmt(stmt: pstmt): pstmt =
      stmt match {
        case u: uAssg => u
        case c: cAssg => {
          if (c.cnd == Vector(in.BoolLit(true)(finfo)) || c.cnd == Vector()) {
            println("optimizing true path condition", c)
            return new uAssg(c.v, c.newval)
          }
          println("unoptimized path condition", c.v, c.cnd, c.newval, c.oldval)
          c
        }
      }
    args.foreach(a => setVar(a.id, a))
    res.foreach(a => setVar(a.id, in.DfltVal(a.typ)(finfo)))

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
    // val overflowPosts =
    //   transformed.map(OverflowChecksTransform.getPureBlockPosts(_, func.results)).getOrElse((Vector()))
    // val vOverflowPosts = overflowPosts.map(ctx.ass.postcondition(_)(ctx))

    for {
      pres <- sequence(vArgPres ++ func.pres.map(ctx.ass.precondition(_)(ctx)))
      posts <- sequence(
        //vResultPosts ++ vOverflowPosts ++ func.posts.map(ctx.ass.postcondition(_)(ctx).map(fixResultvar(_)))
        vResultPosts ++ func.posts.map(ctx.ass.postcondition(_)(ctx).map(fixResultvar(_)))
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
