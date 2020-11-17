// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.gobra.ast.internal.transform

import viper.gobra.ast.internal._
import viper.gobra.reporting.Source
import viper.gobra.reporting.Source.Parser.Single
import viper.gobra.util.TypeBounds.BoundedIntegerKind
import viper.gobra.util.Violation.violation

/**
  * Adds overflow checks to programs written in Gobra's internal language
  */
object OverflowChecksTransform extends InternalTransform {
  override def name(): String = "add_integer_overflow_checks"

  override def transform(p: Program): Program = transformMembers(memberTrans)(p)

  private def memberTrans(member: Member): Member =
    member match {
      // adds overflow checks per statement that contains subexpressions of bounded integer type and adds assume
      /// statements at the beginning of a function or method body assuming that the value of an argument (of
      // bounded integer type) respects the bounds.
      case f @ Function(name, args, results, pres, posts, body) =>
        Function(name, args, results, pres, posts, body map computeNewBody)(f.info)

      // same as functions
      case m @ Method(receiver, name, args, results, pres, posts, body) =>
        Method(receiver, name, args, results, pres, posts, body map computeNewBody)(m.info)

      // Adds pre-conditions stating the bounds of each argument and a post-condition to check if the body expression
      // overflows
      case f @ PureFunction(name, args, results, pres, posts, body) =>
        body match {
          case Some(block) =>
            val newPost = posts // ++ getPureBlockPosts(block, results) todo
            PureFunction(name, args, results, pres, newPost, body)(f.info)
          case None => f
        }

      // Same as pure functions
      case m @ PureMethod(receiver, name, args, results, pres, posts, body) =>
        body match {
          case Some(block) =>
            val newPost = posts // ++ getPureBlockPosts(block, results) todo
            PureMethod(receiver, name, args, results, pres, newPost, body)(m.info)
          case None => m
        }

      /* As discussed on the Gobra meeting (27/10/2020), overflow checks should not be added to predicates, assertions
       * and any other purely logical (i.e. non-executable code) statements and expressions. This seems to be the approach taken
       * by other verification tools such as FramaC, as noted by Wytse
       */

      case x => x
    }

  /**
    * Adds overflow checks to the body of a block.
    */
  private def computeNewBody(body: Block): Block = {
    val blockStmts = body.stmts map stmtTransform
    Block(body.decls, blockStmts)(body.info)
  }

  /**
    * Computes the post-conditions to be added to pure functions and methods to check for overflows, i.e.
    * that the expression result is within the bounds of its type
    */
  def getPureBlockPosts(body: Expr, results: Vector[Parameter.Out]): Vector[Assertion] = {
    // relies on the current assumption that pure functions and methods must have exactly one result argument
    if (results.length != 1) violation("Pure functions and methods must have exactly one result argument")
    Vector(assertionExprInBounds(body, results(0).typ)(createAnnotatedInfo(body.info)))
  }

  private def stmtTransform(stmt: Stmt): Stmt =
    stmt match {
      case b @ Block(decls, stmts) => Block(decls, stmts map stmtTransform)(b.info)

      case s @ Seqn(stmts) => Seqn(stmts map stmtTransform)(s.info)

      case i @ If(cond, thn, els) =>
        val condInfo = createAnnotatedInfo(cond.info)
        val assertCond = Assert(assertionExprInBounds(cond, cond.typ)(condInfo))(condInfo)
        val ifStmt = If(cond, stmtTransform(thn), stmtTransform(els))(i.info)
        Seqn(Vector(assertCond, ifStmt))(i.info)

      case w @ While(cond, invs, body) =>
        val condInfo = createAnnotatedInfo(cond.info)
        val assertCond = Assert(assertionExprInBounds(cond, cond.typ)(condInfo))(condInfo)
        val whileStmt = While(cond, invs, stmtTransform(body))(w.info)
        Seqn(Vector(assertCond, whileStmt))(w.info)

      case ass @ SingleAss(l, r) =>
        val info = createAnnotatedInfo(r.info)
        val assertBounds = Assert(assertionExprInBounds(r, l.op.typ)(info))(info)
        Seqn(Vector(assertBounds, ass))(l.op.info)

      case f @ FunctionCall(_, _, args) =>
        val asserts = args map (expr => {
          val info = createAnnotatedInfo(expr.info)
          Assert(assertionExprInBounds(expr, expr.typ)(info))(info)
        })
        Seqn(f +: asserts)(f.info)

      case m @ MethodCall(_, recv, _, args) =>
        val asserts = args map (expr => {
          val info = createAnnotatedInfo(expr.info)
          Assert(assertionExprInBounds(expr, expr.typ)(info))(info)
        })
        val recvInfo = createAnnotatedInfo(recv.info)
        val recvAssert = Assert(assertionExprInBounds(recv, recv.typ)(recvInfo))(recvInfo)
        Seqn(m +: recvAssert +: asserts)(m.info)

      case m @ Make(_, typ) =>
        val info = createAnnotatedInfo(typ.info)
        val assertBounds = Assert(assertionExprInBounds(typ.op, typ.op.typ)(info))(info)
        Seqn(Vector(assertBounds, m))(m.info)

      // explicitly matches remaining statements to detect non-exhaustive pattern matching if a new statement is added
      case x @ (_: Inhale | _: Exhale | _: Assert | _: Assume | _: Return | _: Fold | _: Unfold) => x
    }

  // Checks if expr and its subexpressions are within bounds of type `typ`
  private def assertionExprInBounds(expr: Expr, typ: Type)(info: Source.Parser.Info): Assertion = {
    val trueLit: Expr = BoolLit(true)(info)

    def genAssertionExpr(expr: Expr, typ: Type): Expr =
      typ match {
        case IntT(_, kind) if kind.isInstanceOf[BoundedIntegerKind] =>
          val boundedKind = kind.asInstanceOf[BoundedIntegerKind]
          And(
            AtMostCmp(IntLit(boundedKind.lower)(info), expr)(info),
            AtMostCmp(expr, IntLit(boundedKind.upper)(info))(info)
          )(info)

        case _ => trueLit
      }

    val intSubExprs: Set[Expr] = Expr.getSubExpressions(expr).filter(_.typ.isInstanceOf[IntT])

    // values assumed to be within bounds, i.e. variables, fields from structs, dereferences of pointers and indexed expressions
    // this stops Gobra from throwing overflow errors in field accesses and pointer dereferences because Gobra was not able to prove that
    // they were within bounds even though that is guaranteed by the expression's type
    val valuesWithinBounds = intSubExprs.filter {
      case _: Var | _: FieldRef | _: IndexedExp | _: Deref => true
      case _                                               => false
    }

    val computeAssertions = (exprs: Set[Expr]) =>
      exprs.map { x => genAssertionExpr(x, x.typ) }.foldRight(trueLit)((x, y) => And(x, y)(info))

    // assumptions for the values that are considered within bounds
    val assumptions = computeAssertions(valuesWithinBounds)

    // Assertions that need to be verified assuming the expressions in `assumptions`
    val obligations = ExprAssertion(computeAssertions(intSubExprs))(info)
    Implication(assumptions, obligations)(info)
  }

  // should this be moved to Source class?
  case object OverflowCheckAnnotation extends Source.Annotation

  private def createAnnotatedInfo(info: Source.Parser.Info): Source.Parser.Info =
    info match {
      case s: Single => s.createAnnotatedInfo(OverflowCheckAnnotation)
      case i         => violation(s"l.op.info ($i) is expected to be a Single")
    }
}
