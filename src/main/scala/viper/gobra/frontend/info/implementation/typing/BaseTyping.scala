// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2020 ETH Zurich.

package viper.gobra.frontend.info.implementation.typing

import org.bitbucket.inkytonik.kiama.==>
import org.bitbucket.inkytonik.kiama.util.Messaging.{Messages, noMessages}
import viper.gobra.ast.frontend._
import viper.gobra.frontend.info.base.Type.{Type, UnknownType}
import viper.gobra.frontend.info.implementation.TypeInfoImpl
import viper.gobra.util.Safety


trait BaseTyping { this: TypeInfoImpl =>

  import org.bitbucket.inkytonik.kiama.attribution.Attribution
  import viper.gobra.util.{Memoization, Validity}

  sealed trait ValidityMessages {
    def out: Messages
    def valid: Boolean
  }

  private[typing] case object UnsafeForwardMessage extends ValidityMessages {
    override val out: Messages = noMessages
    override val valid: Boolean = false
  }

  private[typing] def unsafeMessage(cond: Boolean): ValidityMessages =
    if (cond) UnsafeForwardMessage else LocalMessages(noMessages)

  private[typing] case class LocalMessages(override val out: Messages) extends ValidityMessages {
    override def valid: Boolean = out.isEmpty
  }

  trait Error[-A] extends Validity[A, ValidityMessages] {
    override def invalid(ret: ValidityMessages): Boolean = !ret.valid
  }

  def allChildren(n: PNode): Vector[PNode] = {
    tree.child(n).flatMap(m => m +: allChildren(m))
  }

  trait WellDefinedness[-A] extends Error[A]

  private[typing] def children[T <: PNode](n: T): Vector[PNode] =
    tree.child(n)

  private[typing] def childrenWellDefined(n: PNode): Boolean = children(n) forall selfWellDefined

  private[typing] def selfWellDefined(n: PNode): Boolean = n match {
    case s: PStatement => wellDefStmt.valid(s)
    case n: PExpressionAndType => wellDefExprAndType.valid(n)
    case e: PExpression => wellDefExpr.valid(e)
    case t: PType => wellDefType.valid(t)
    case i: PIdnNode => wellDefID.valid(i)
    case o: PMisc => wellDefMisc.valid(o)
    case s: PSpecification => wellDefSpec.valid(s)
    case m: PNode => childrenWellDefined(m)
  }

  private[typing] def createWellDef[T <: PNode](check: T => Messages): WellDefinedness[T] =
    new Attribution with WellDefinedness[T] with Safety[T, ValidityMessages] with Memoization[T, ValidityMessages] {

      override def safe(n: T): Boolean = childrenWellDefined(n)

      override def unsafe: ValidityMessages = UnsafeForwardMessage

      override def compute(n: T): ValidityMessages = LocalMessages(check(n))
    }

  private[typing] def createWellDefWithValidityMessages[T <: PNode](check: T => ValidityMessages): WellDefinedness[T] =
    new Attribution with WellDefinedness[T] with Safety[T, ValidityMessages] with Memoization[T, ValidityMessages] {

      override def safe(n: T): Boolean = childrenWellDefined(n)

      override def unsafe: ValidityMessages = UnsafeForwardMessage

      override def compute(n: T): ValidityMessages = check(n)
    }

  private[typing] def createIndependentWellDef[T <: PNode](check: T ==> Messages)(pre: T => Boolean): WellDefinedness[T] =
    new Attribution with WellDefinedness[T] with Safety[T, ValidityMessages] with Memoization[T, ValidityMessages] {

    override def safe(n: T): Boolean = pre(n)

    override def unsafe: ValidityMessages = UnsafeForwardMessage

    override def compute(n: T): ValidityMessages =
      LocalMessages(if (check.isDefinedAt(n)) check(n) else noMessages)
  }

  trait Typing[-A] extends Safety[A, Type] with Validity[A, Type] {

    override def unsafe: Type = UnknownType

    override def invalid(ret: Type): Boolean = ret == UnknownType
  }

  private[typing] def createTyping[T](inference: T => Type)(implicit wellDef: WellDefinedness[T]): Typing[T] =
    new Attribution with Typing[T] with Memoization[T, Type] {

      override def safe(n: T): Boolean = wellDef.valid(n)

      override def compute(n: T): Type = inference(n)
    }

  private[typing] def createWellDefInference[X, Z](wellDef: X => Boolean)(inference: X => Z): X => Option[Z] =
    new Attribution with Safety[X, Option[Z]] with Memoization[X, Option[Z]] {

      override def safe(n: X): Boolean = wellDef(n)

      override def unsafe: Option[Z] = None

      override def compute(n: X): Option[Z] = Some(inference(n))
    }


}
