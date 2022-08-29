/**
 * HasLang syntax analyser.
 *
 * Copyright 2021, Anthony Sloane, Matthew Roberts, Kym Haines, Macquarie University, All rights reserved.
 */

package haslang

import org.bitbucket.inkytonik.kiama.parsing.Parsers
import org.bitbucket.inkytonik.kiama.util.Positions

/**
 * Module containing parsers for HasLang.
 */
class SyntaxAnalysis (positions : Positions) extends Parsers (positions) {

    import HasLangTree._
    import scala.language.postfixOps

    lazy val parser : PackratParser[Program] =
        phrase (program)

    lazy val program : PackratParser[Program] =
        exp ^^ Program

    lazy val literal : PackratParser[Exp] =
        "false" ^^^ BoolExp (false) |
        "true" ^^^ BoolExp (true) |
        integer ^^ (s => IntExp (s.toInt))

    lazy val factor : PackratParser[Exp] =
        // FIXME
        literal |
        identifier ^^ IdnUse |
        "[" ~> repsep(exp, ",") <~ "]" ^^ ListExp |
        "(" ~> exp <~ ")" |
        "(" ~> rep1sep(exp, ",") <~ ")" ^^ TupleExp |
        failure ("exp expected")

    lazy val exp1 : PackratParser[Exp] =
        exp1 ~ factor ^^ AppExp |
        ("let" ~> definitions) ~ ("in" ~> exp) ^^ LetExp |
        ("\\" ~> idndef) ~ ("->" ~> exp) ^^ LamExp |
        factor

    lazy val exp2 : PackratParser[Exp] =
        (exp2 <~ "*") ~ exp1 ^^ StarExp |
        (exp1 <~ "/") ~ exp2 ^^ SlashExp |    // right assoc
        exp1

    lazy val exp3 : PackratParser[Exp] =
        (exp3 <~ "+") ~ exp2 ^^ PlusExp |
        (exp2 <~ "-") ~ exp3 ^^ MinusExp |    // right assoc
        exp2

    lazy val consterm : PackratParser[Exp] =
        (exp3 <~ ":") ~ consterm ^^ ConsExp |
        exp3

    lazy val condterm : PackratParser[Exp] =
        (consterm <~ "<") ~ consterm ^^ LessExp |
        (consterm <~ "==") ~ consterm ^^ EqualExp |
        consterm

    // FIXME   add parsers between factor and exp

    lazy val exp : PackratParser[Exp] =
        // FIXME
        ("if" ~> "(" ~> exp <~ ")") ~ ("then" ~> exp) ~ ("else" ~> exp) ^^
               IfExp |
        condterm

    lazy val definitions : PackratParser[Vector[Defn]] =
        // FIXME
        rep1sep(defn, ";")

    lazy val defn : PackratParser[Defn] =
        // FIXME
        idndef ~ ("=" ~> exp) ^^
                    {case i ~ e => Defn(i, Vector(FunLine("", Vector(), e)))} |
        idndef ~ rep1sep(funline, ".") ^^ Defn

    lazy val funline : PackratParser[FunLine] =
        // FIXME
        identifier ~ (pat*) ~ ("=" ~> exp) ^^ FunLine

    lazy val pat : PackratParser[Pat] =
        // FIXME
        (pat <~ ":") ~ pat ^^ ConsPat |
        basicpat

    lazy val basicpat : PackratParser[Pat] =
        // FIXME
        literal ^^ LiteralPat |
        identifier ^^ IdentPat |
        "_" ^^ (_ => AnyPat ()) |
        "[" ~> repsep(pat, ",") <~ "]" ^^ ListPat |
        "(" ~> pat <~ ")" |
        "(" ~> rep1sep(pat, ",") <~ ")" ^^ TuplePat

    lazy val tipe : PackratParser[Type] =
        // FIXME
        basictipe ~ ("->" ~> tipe) ^^ FunType |
        basictipe

    lazy val basictipe : PackratParser[Type] =
        // FIXME
        "Bool" ^^^ BoolType () |
        "Int" ^^^ IntType () |
        "(" ~ ")" ^^^ UnitType () |
        "[" ~> tipe <~ "]" ^^ ListType |
        "(" ~> tipe <~ ")" |
        "(" ~> rep1sep(tipe, ",") <~ ")" ^^ TupleType

    // NOTE: You should not change anything below here...

    lazy val integer =
        regex ("[0-9]+".r)

    lazy val idndef =
        (identifier <~ "::") ~ tipe ^^ IdnDef

    val keywordStrings =
        List ("let", "else", "false", "if", "then", "true", "in")

    lazy val keyword =
        keywords ("[^a-zA-Z0-9_]".r, keywordStrings)

    lazy val identifier =
        not (keyword) ~> identifierBase

    lazy val identifierBase =
        regex ("[a-zA-Z][a-zA-Z0-9_]*".r) |
        failure ("identifier expected")

    lazy val whitespaceParser : PackratParser[Any] =
        rep ( """\s""".r | comment)

    lazy val comment : PackratParser[Any] =
        "{-" ~ rep (not ("-}") ~ (comment | any)) ~ "-}" |
        "--.*(\n|\\z)".r

}