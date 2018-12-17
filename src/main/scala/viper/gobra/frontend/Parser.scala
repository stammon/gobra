/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.gobra.frontend

import java.io.File

import org.bitbucket.inkytonik.kiama.parsing.Parsers
import org.bitbucket.inkytonik.kiama.util.Positions
import viper.gobra.ast.parser._
import viper.gobra.reporting.VerifierError

object Parser {

  def parse(file: File): Either[Vector[VerifierError], PProgram] = {
    Left(Vector.empty)
  }

  private class PureSyntaxAnalyzer(positions: Positions) extends Parsers(positions) {

    val reservedWords: Set[String] = Set(
      "break", "default", "func", "interface", "select",
      "case", "defer", "go", "map", "struct",
      "chan", "else", "goto", "package", "switch",
      "const", "fallthrough", "if", "range", "type",
      "continue", "for", "import", "return", "var"
    )

    def isReservedWord(word: String): Boolean = reservedWords contains word

    /**
      * Statements
      */

    lazy val statement: Parser[PStatement] = ???

    lazy val simpleStmt: Parser[PSimpleStmt] = ???

    lazy val simpleStmtWithEmpty: Parser[PSimpleStmt] =
      simpleStmt | emptyStmt

    lazy val emptyStmt: Parser[PEmptyStmt] = /* parse last because always succeeds */
      success(PEmptyStmt())

    lazy val expressionStmt: Parser[PExpressionStmt] =
      expression ^^ PExpressionStmt

    lazy val sendStmt: Parser[PSendStmt] =
      (expression <~ "<-") ~ expression ^^ PSendStmt

    lazy val assignment: Parser[PAssignment] = ???

    lazy val assignee: Parser[PAssignee] =
      selectionOrMethodExpr | selection | indexedExp | "&" ~> unaryExp ^^ PDereference

    /**
      * Expressions
      */

    lazy val expression: Parser[PExpression] =
      precedence1

    lazy val precedence1: Parser[PExpression] = /* Left-associative */
      precedence1 ~ ("||" ~> precedence2) ^^ POr |
        precedence2

    lazy val precedence2: Parser[PExpression] = /* Left-associative */
      precedence2 ~ ("&&" ~> precedence3) ^^ PAnd |
        precedence3

    lazy val precedence3: Parser[PExpression] = /* Left-associative */
      precedence3 ~ ("==" ~> precedence4) ^^ PEquals |
        precedence3 ~ ("!=" ~> precedence4) ^^ PUnequals |
        precedence3 ~ ("<" ~> precedence4) ^^ PLess |
        precedence3 ~ ("<=" ~> precedence4) ^^ PAtMost |
        precedence3 ~ (">" ~> precedence4) ^^ PGreater |
        precedence3 ~ (">=" ~> precedence4) ^^ PAtLeast |
        precedence4

    lazy val precedence4: Parser[PExpression] = /* Left-associative */
      precedence4 ~ ("+" ~> precedence5) ^^ PAdd |
        precedence4 ~ ("-" ~> precedence5) ^^ PSub |
        precedence3

    lazy val precedence5: Parser[PExpression] = /* Left-associative */
      precedence5 ~ ("*" ~> precedence6) ^^ PMul |
        precedence5 ~ ("/" ~> precedence6) ^^ PDiv |
        precedence5 ~ ("%" ~> precedence6) ^^ PMod |
        precedence6

    lazy val precedence6: Parser[PExpression] =
      unaryExp


    lazy val unaryExp: Parser[PExpression] =
      "+" ~> unaryExp ^^ PUnaryPlus |
        "-" ~> unaryExp ^^ PUnaryMinus |
        "!" ~> unaryExp ^^ PNegation |
        "*" ~> unaryExp ^^ PReference |
        "&" ~> unaryExp ^^ PDereference |
        "<-" ~> unaryExp ^^ PReceive |
        primaryExp


    lazy val primaryExp: Parser[PExpression] =
      operand |
        conversionOrUnaryCall |
        conversion |
        call |
        selectionOrMethodExpr |
        methodExpr |
        selection |
        indexedExp |
        sliceExp |
        typeAssertion

    lazy val operand: Parser[PExpression] =
      literal | namedOperand | "(" ~> expression <~ ")"

    lazy val namedOperand: Parser[PNamedOperand] =
      idnUse ^^ PNamedOperand

    lazy val literal: Parser[PLiteral] =
      basicLit | compositeLit | functionLit

    lazy val basicLit: Parser[PBasicLiteral] =
      "true" ^^^ PBoolLit(true) |
        "false" ^^^ PBoolLit(false) |
        "nil" ^^^ PNilLit() |
        regex("[0-9]+".r) ^^ (lit => PIntLit(BigInt(lit)))

    lazy val compositeLit: Parser[PCompositeLit] =
      literalType ~ literalValue ^^ PCompositeLit

    lazy val literalValue: Parser[PLiteralValue] =
      "{" ~> (rep1sep(keyedElement, ",") <~ ",".?).? <~ "}" ^^ {
        case None => PLiteralValue(Vector.empty)
        case Some(ps) => PLiteralValue(ps)
      }

    lazy val keyedElement: Parser[PKeyedElement] =
      (compositeVal <~ ":").? ~ compositeVal ^^ PKeyedElement

    lazy val compositeVal: Parser[PCompositeVal] =
      expCompositeLiteral | litCompositeLiteral

    lazy val expCompositeLiteral: Parser[PExpCompositeVal] =
      expression ^^ PExpCompositeVal

    lazy val litCompositeLiteral: Parser[PLitCompositeVal] =
      literalValue ^^ PLitCompositeVal

    lazy val functionLit: Parser[PFunctionLit] =
      "func" ~> signature ~ block ^^ { case sig ~ body => PFunctionLit(sig._1, sig._2, body) }

    lazy val conversionOrUnaryCall: Parser[PConversionOrUnaryCall] =
      nestedIdnUse ~ ("(" ~> expression <~ ",".? <~ ")") ^^ {
        PConversionOrUnaryCall
      }

    lazy val conversion: Parser[PConversion] =
      typ ~ ("(" ~> expression <~ ",".? <~ ")") ^^ PConversion

    lazy val call: Parser[PCall] =
      primaryExp ~ ("(" ~> (rep1sep(expression, ",") <~ ",".?).? <~ ")") ^^ {
        case base ~ None => PCall(base, Vector.empty)
        case base ~ Some(args) => PCall(base, args)
      }

    lazy val selectionOrMethodExpr: Parser[PSelectionOrMethodExpr] =
      nestedIdnUse ~ ("." ~> idnUnqualifiedUse) ^^ PSelectionOrMethodExpr

    lazy val methodExpr: Parser[PMethodExpr] =
      methodRecv ~ ("." ~> idnUnqualifiedUse) ^^ PMethodExpr

    lazy val selection: Parser[PSelection] =
      primaryExp ~ ("." ~> idnUnqualifiedUse) ^^ PSelection

    lazy val indexedExp: Parser[PIndexedExp] =
      primaryExp ~ ("[" ~> expression <~ "]") ^^ PIndexedExp

    lazy val sliceExp: Parser[PSliceExp] =
      primaryExp ~ ("[" ~> expression) ~ ("," ~> expression) ~ (("," ~> expression).? <~ "]") ^^ PSliceExp

    lazy val typeAssertion: Parser[PTypeAssertion] =
      primaryExp ~ ("." ~> "(" ~> typ <~ ")") ^^ PTypeAssertion


    /**
      * Types
      */

    lazy val typ: Parser[PType] =
      "(" ~> typ <~ ")" | typeLit | namedType

    lazy val typeLit: Parser[PTypeLit] =
      pointerType | sliceType | arrayType | mapType | channelType | functionType | structType | interfaceType


    lazy val pointerType: Parser[PPointerType] =
      "*" ~> typ ^^ PPointerType

    lazy val sliceType: Parser[PSliceType] =
      "[]" ~> typ ^^ PSliceType

    lazy val mapType: Parser[PMapType] =
      ("map" ~> ("[" ~> typ <~ "]")) ~ typ ^^ PMapType

    lazy val channelType: Parser[PChannelType] =
      ("chan" ~> "<-") ~> typ ^^ PRecvChannelType |
        ("<-" ~> "chan") ~> typ ^^ PSendChannelType |
        "chan" ~> typ ^^ PBiChannelType

    lazy val functionType: Parser[PFunctionType] =
      "func" ~> signature ^^ PFunctionType.tupled

    lazy val arrayType: Parser[PArrayType] =
      ("[" ~> expression <~ "]") ~ typ ^^ PArrayType

    lazy val structType: Parser[PStructType] =
      "struct" ~> "{" ~> repsep(structClause, eos) <~ "}" ^^ { clauses =>
        val embedded = clauses collect { case v: PEmbeddedDecl => v }
        val declss = clauses collect { case v: PFieldDecls => v }

        PStructType(embedded, declss flatMap (_.fields))
      }

    lazy val structClause: Parser[PStructClause] =
      embeddedDecl | fieldDecls

    lazy val embeddedDecl: Parser[PEmbeddedDecl] =
      "*".? ~ namedType ^^ {
        case None ~ t => PEmbeddedName(t)
        case _ ~ t => PEmbeddedPointer(t)
      }

    lazy val fieldDecls: Parser[PFieldDecls] =
      rep1sep(idnDef, ",") ~ typ ^^ { case ids ~ t =>
        PFieldDecls(ids map (PFieldDecl(_, t)))
      }

    lazy val interfaceType: Parser[PInterfaceType] =
      "interface" ~> "{" ~> repsep(interfaceClause, eos) <~ "}" ^^ { clauses =>
        val embedded = clauses collect { case v: PInterfaceName => v }
        val decls = clauses collect { case v: PMethodSpec => v }

        PInterfaceType(embedded, decls)
      }

    lazy val interfaceClause: Parser[PInterfaceClause] =
      methodSpec | interfaceName

    lazy val interfaceName: Parser[PInterfaceName] =
      namedType ^^ PInterfaceName

    lazy val methodSpec: Parser[PMethodSpec] =
      idnDef ~ signature ^^ { case id ~ sig => PMethodSpec(id, sig._1, sig._2) }


    lazy val namedType: Parser[PNamedType] =
      predeclaredType |
        declaredType

    lazy val predeclaredType: Parser[PPredeclaredType] =
      "bool" ^^^ PBoolType() |
        "int" ^^^ PIntType()

    lazy val declaredType: Parser[PDeclaredType] =
      idnUse ^^ PDeclaredType

    lazy val literalType: Parser[PLiteralType] =
      sliceType | arrayType | implicitSizeArrayType | mapType | structType

    lazy val implicitSizeArrayType: Parser[PImplicitSizeArrayType] =
      "[" ~> "..." ~> "]" ~> typ ^^ PImplicitSizeArrayType

    /**
      * Misc
      */

    lazy val signature: Parser[(Vector[PParameter], PResult)] =
      parameters ~ result

    lazy val block: Parser[PBlock] =
      "{" ~> repsep(statement, eos) <~ "}" ^^ PBlock


    lazy val result: Parser[PResult] =
      parameters ^^ PResultClause |
        typ ^^ (t => PResultClause(Vector(PUnnamedParameter(t)))) |
        success(PVoidResult())

    lazy val parameters: Parser[Vector[PParameter]] =
      "(" ~> (parameters <~ ",".?).? <~ ")" ^^ {
        case None => Vector.empty
        case Some(ps) => ps
      }

    lazy val parameterList: Parser[Vector[PParameter]] =
      rep1sep(parameterDecl, ",") ^^ Vector.concat

    lazy val parameterDecl: Parser[Vector[PParameter]] =
      repsep(idnDef, ",") ~ typ ^^ { case ids ~ t =>

        val names = ids filter (!PIdnNode.isWildcard(_))
        if (names.isEmpty) {
          Vector(PUnnamedParameter(t))
        } else {
          ids map (PNamedParameter(_, t))
        }
      }

    lazy val nestedIdnUse: Parser[PIdnUse] =
      "(" ~> nestedIdnUse <~ ")" | idnUse

    lazy val methodRecv: Parser[PMethodRecv] =
      "(" ~> methodRecv <~ ")" | embeddedDecl


    /**
      * Identifiers
      */

    lazy val idnUnknown: Parser[PIdnUnknown] =
      identifier ^^ PIdnUnknown

    lazy val idnDef: Parser[PIdnDef] =
      identifier ^^ PIdnDef

    lazy val idnUse: Parser[PIdnUse] =
      idnUnqualifiedUse

    lazy val idnUnqualifiedUse: Parser[PIdnUnqualifiedUse] =
      identifier ^^ PIdnUnqualifiedUse

    lazy val identifier: Parser[String] =
      "[a-zA-Z_][a-zA-Z0-9_]*".r into (s => {
        if (isReservedWord(s))
          failure(s"""keyword "$s" found where identifier expected""")
        else
          success(s)
      })

    /**
      * EOS
      */

    lazy val eos: Parser[String] =
      ";"
  }


}


