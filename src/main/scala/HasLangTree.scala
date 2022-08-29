/**
 * HasLang source program tree definition.
 *
 * Copyright 2021, Anthony Sloane, Matthew Roberts, Kym Haines, Macquarie University, All rights reserved.
 */

package haslang

/**
 * Module containing tree structures for representing HasLang programs.
 */
object HasLangTree {

    /**
     * The common supertype of all source tree nodes.
     */
    sealed abstract class HasLangNode

    /**
     * A HasLang program is an expression.
     */
    case class Program (exp : Exp) extends HasLangNode

    /**
     * Common class for all definitions.
     */
    case class Defn (idndef: IdnDef, lines: Vector[FunLine]) extends HasLangNode

    /**
     * Function line
     */
    case class FunLine (ident: String, pats: Vector[Pat], exp : Exp) extends HasLangNode

    /**
     * Base class of all types.
     */
    sealed abstract class Type

    /**
     * Unit type
     */
    case class UnitType () extends Type

    /**
     * Boolean type
     */
    case class BoolType () extends Type

    /**
     * Function type
     */
    case class FunType (from : Type, to : Type) extends Type

    /**
     * Integer type
     */
    case class IntType () extends Type

    /**
     * List type
     */
    case class ListType (elemType : Type) extends Type

    /**
     * Tuple type
     */
    case class TupleType (types : Vector[Type]) extends Type

    /**
     * Base class of all patterns.
     */
    sealed abstract class Pat

    /**
     * Literal pattern
     */
    case class LiteralPat (exp : Exp) extends Pat

    /**
     * Identifier pattern
     */
    case class IdentPat (ident : String) extends Pat

    /**
     * 'Any' pattern
     */
    case class AnyPat () extends Pat

    /**
     * Cons pattern
     */
    case class ConsPat (left : Pat, right : Pat) extends Pat

    /**
     * List pattern
     */
    case class ListPat (pats : Vector[Pat]) extends Pat

    /**
     * Tuple pattern
     */
    case class TuplePat (pats : Vector[Pat]) extends Pat

    /**
     * An unknown type, for example, one belonging to a name that is not declared
     * but is used in an expression.
     */
    case class UnknownType () extends Type

    /**
     * Common superclass of expressions.
     */
    sealed abstract class Exp extends HasLangNode

    /**
     * Application expression.
     */
    case class AppExp (fn : Exp, arg : Exp) extends Exp

     /**
     * Function argument and body (lambda expression).
     */
    case class LamExp (arg : IdnDef, body : Exp) extends Exp

   /**
     * Let expression.
     */
    case class LetExp (defns : Vector[Defn], exp : Exp) extends Exp

    /**
     * Tuple expression
     */
    case class TupleExp (exps : Vector[Exp]) extends Exp

    /**
     * List expression
     */
    case class ListExp (exps : Vector[Exp]) extends Exp

    /**
     * Boolean-valued expression (True or False).
     */
    case class BoolExp (b : Boolean) extends Exp

    /**
     * Equality expression compares the left and right expressions for equality.
     */
    case class EqualExp (left : Exp, right : Exp) extends Exp

    /**
     * Conditional expression.
     */
    case class IfExp (cond : Exp, thenExp : Exp, elseExp : Exp) extends Exp

    /**
     * Integer-valued numeric expression.
     */
    case class IntExp (n : Int) extends Exp

    /**
     * Less than expression compares the left and right numeric expressions for less-than order.
     */
    case class LessExp (left : Exp, right : Exp) extends Exp

    /**
     * An expression whose value is the difference between the values of
     * two expressions.
     */
    case class MinusExp (left : Exp, right : Exp) extends Exp

    /**
     * An expression whose value is the sum of the values of two expressions.
     */
    case class PlusExp (left : Exp, right : Exp) extends Exp

    /**
     * An expression whose value is the division of the values of two expressions.
     */
    case class SlashExp (left : Exp, right : Exp) extends Exp

    /**
     * An expression whose value is the product of the values of two expressions.
     */
    case class StarExp (left : Exp, right : Exp) extends Exp

    /**
     * Cons
     */
    case class ConsExp (left : Exp, right : Exp) extends Exp

    /**
     * An identifier reference.
     */
    sealed trait Idn extends HasLangNode {
        def idn : Identifier
    }

    /**
     * A defining occurrence (def) of an identifier.
     */
    case class IdnDef (idn : Identifier, tipe: Type) extends Idn

    /**
     * An applied occurrence (use) of an identifier.
     */
    case class IdnUse (idn : Identifier) extends Exp with Idn

    /**
     * A representation of identifiers as strings.
     */
    type Identifier = String

}
