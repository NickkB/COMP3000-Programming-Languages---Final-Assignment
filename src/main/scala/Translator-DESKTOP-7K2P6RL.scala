/**
 * HasLang to SEC translator.
 *
 * Copyright 2021, Anthony Sloane, Kym Haines, Macquarie University, All rights reserved.
 */

package haslang

/**
 * Translator from HasLang source programs to SEC target programs.
 */
object Translator {

    import SECTree._
    import HasLangTree._
    import scala.collection.mutable.ListBuffer

    /**
     * Return a frame that represents the SEC instructions for a FunLang program.
     */
    def translate (program : Program) : Frame = {

        // An instruction buffer for accumulating the program instructions
        val programInstrBuffer = new ListBuffer[Instr] ()

        /**
         * Translate the program by translating its expression.
         */
        val expInstrs = translateExpression (program.exp)
        programInstrBuffer.appendAll (expInstrs)
        programInstrBuffer.append (IPrint ())

        // Gather the program's instructions and return them
        programInstrBuffer.result ()

    }

    /**
     * Translate an expression and return a list of the instructions that
     * form the translation.
     */
    def translateExpression (exp : Exp) : Frame = {

        // An instruction buffer for accumulating the expression instructions
        val expInstrBuffer = new ListBuffer[Instr] ()

        /**
         * Generate an instruction by appending it to the instruction buffer.
         */
        def gen (instr : Instr) {
            expInstrBuffer.append (instr)
        }

        /**
         * Generate a sequence of instructions by appending them all to the
         * instruction buffer.
         */
        def genall (frame : Frame) {
            expInstrBuffer.appendAll (frame)
        }

        /**
         * Generate code to make a closure (argName => body).
         */
        def genMkClosure (argName : String, body : Exp) {
            val bodyInstrs = translateExpression (body)
            gen (IClosure (argName, bodyInstrs :+ IPopEnv ()))
        }

        def LetFunc (in : Vector[Pat]) = in match {

            case AnyPat() +: t => translateExpression(AppExp(IdnUse("tail"), IdnUse("x")))

        }

        exp match {

        case IdnUse (value) =>
            gen (IVar (value))

        case IntExp (value) =>
            gen (IInt (value))

        case BoolExp (value) =>
            gen (IBool (value))

        case PlusExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (IAdd ())

        case MinusExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (ISub ())

        case SlashExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (IDiv ())

        case StarExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (IMul ())

        case LessExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (ILess ())

        case EqualExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (IEqual ())

        case LamExp (IdnDef (name, _), body) =>
            genMkClosure(name, body)

        case ConsExp (l, r) =>
            genall (translateExpression (l))
            genall (translateExpression (r))
            gen (ICons ())

        case IfExp (c, l, r) =>
            genall (translateExpression (c))
            gen (IBranch (translateExpression (l), translateExpression (r)))

        case AppExp (IdnUse("head"), arg) =>  
            genall (translateExpression (arg))
            gen (IHead())

        case AppExp (IdnUse("tail"), arg) =>
            genall (translateExpression (arg))
            gen (ITail())

        case AppExp (IdnUse("length"), arg) =>
            genall (translateExpression (arg))
            gen (ILength())

        case AppExp (fn, arg) =>
            genall (translateExpression(fn))
            genall (translateExpression(arg))
            gen (ICall ())

        case ListExp (Vector()) => 
            gen (INil ())

        case ListExp (Vector(arg)) => 
            genall (translateExpression (arg))
            gen (INil ())
            gen (ICons ())

        case ListExp (h +: t) => 
            genall (translateExpression (h))
            genall (translateExpression (ListExp(t)))
            gen (ICons ()) 

        case LetExp (Vector(Defn(name, Vector(FunLine("", Vector(), exp)))), body) =>
            genall (translateExpression(AppExp(LamExp(name, body), exp)))

        case LetExp (Defn(name, Vector(FunLine("", Vector(), exp))) +: t, body) =>
            genall (translateExpression(LetExp(Vector(Defn(name, Vector(FunLine("", Vector(), exp)))), LetExp(t, body))))
       
        case LetExp (Vector(Defn(name, Vector(FunLine(func,Vector(LiteralPat(pat)), exp)))), body) =>
            genall (translateExpression(AppExp(LamExp(name, body), LamExp(IdnDef("x", UnknownType()), IfExp(EqualExp(IdnUse("x"), pat), exp, IntExp(999))))))

        case LetExp (Vector(Defn(name, Vector(FunLine(func,Vector(IdentPat(pat)), exp)))), body) =>
            genall (translateExpression(AppExp(LamExp(name, body), LamExp(IdnDef("x", UnknownType()), AppExp(LamExp(IdnDef(pat, UnknownType()), exp), IdnUse("x"))))))

        case LetExp (Vector(Defn(name, Vector(FunLine(func,Vector(AnyPat()), exp)))), body) =>
            genall (translateExpression(AppExp(LamExp(name, body), LamExp(IdnDef("x", UnknownType()), exp))))

        case LetExp (Vector(Defn(name, Vector(FunLine(func,Vector(ConsPat(LiteralPat(a), b)), exp)))), body) =>
            genall (translateExpression(AppExp(LamExp(name, body), LamExp(IdnDef("x", UnknownType()), IfExp(LessExp(AppExp(IdnUse("length"), IdnUse("x")), IntExp(1)), 
                                                                                                            IntExp(999), IfExp(EqualExp(AppExp(IdnUse("head"), IdnUse("x")), a), exp, IntExp(999)))))))

        case LetExp (Vector(Defn(name, Vector(FunLine(func,Vector(ListPat(Vector())), exp)))), body) =>
            genall (translateExpression(AppExp(LamExp(name, body), LamExp(IdnDef("x", UnknownType()), IfExp(EqualExp(AppExp(IdnUse("length"), IdnUse("x")), IntExp(0)), exp, IntExp(999))))))

        case LetExp (Vector(Defn(name, Vector(FunLine(func,Vector(ListPat(Vector(LiteralPat(a)))), exp)))), body) =>
            genall (translateExpression(AppExp(LamExp(name, body), LamExp(IdnDef("x", UnknownType()), IfExp(EqualExp(AppExp(IdnUse("length"), IdnUse("x")), IntExp(1)), 
                                                                                                            IfExp(EqualExp(AppExp(IdnUse("head"), IdnUse("x")), a), exp, IntExp(999)), IntExp(999))))))

        case LetExp (Vector(Defn(name, Vector(FunLine(func,Vector(ListPat(Vector(IdentPat(a)))), exp)))), body) =>
            genall (translateExpression(AppExp(LamExp(name, body), LamExp(IdnDef("x", UnknownType()), IfExp(EqualExp(AppExp(IdnUse("length"), IdnUse("x")), IntExp(1)), 
                                                                                                            AppExp(LamExp(IdnDef(a, UnknownType()), exp), AppExp(IdnUse("head"), IdnUse("x"))), IntExp(999))))))

        case LetExp(Vector(Defn(name, Vector(FunLine(func,Vector(ListPat(Vector(AnyPat(), IdentPat(a)))), exp)))), body) =>
            genall (translateExpression(AppExp(LamExp(name, body), LamExp(IdnDef("x", UnknownType()), IfExp(EqualExp(AppExp(IdnUse("length"), IdnUse("x")), IntExp(2)), 
                                                                                                            AppExp(LamExp(IdnDef(a, UnknownType()), exp), AppExp(IdnUse("head"), AppExp(IdnUse("tail"), IdnUse("x")))), IntExp(999))))))
        
        case LetExp(Vector(Defn(name, Vector(FunLine(func,Vector(ListPat(Vector(AnyPat(), AnyPat(), IdentPat(a)))), exp)))), body) =>
            genall (translateExpression(AppExp(LamExp(name, body), LamExp(IdnDef("x", UnknownType()), IfExp(EqualExp(AppExp(IdnUse("length"), IdnUse("x")), IntExp(3)), 
                                                                                                            AppExp(LamExp(IdnDef(a, UnknownType()), exp), AppExp(IdnUse("head"), AppExp(IdnUse("tail"), AppExp(IdnUse("tail"), IdnUse("x"))))), IntExp(999))))))

        case LetExp(Vector(Defn(name, Vector(FunLine(func,Vector(ListPat(Vector(AnyPat(), IdentPat(a), AnyPat()))), exp)))), body) =>
            genall (translateExpression(AppExp(LamExp(name, body), LamExp(IdnDef("x", UnknownType()), IfExp(EqualExp(AppExp(IdnUse("length"), IdnUse("x")), IntExp(3)), 
                                                                                                            AppExp(LamExp(IdnDef(a, UnknownType()), exp), AppExp(IdnUse("head"), AppExp(IdnUse("tail"), IdnUse("x")))), IntExp(999))))))

        case LetExp(Vector(Defn(name, Vector(FunLine(func,Vector(ListPat(Vector(IdentPat(a), AnyPat(), AnyPat()))), exp)))), body) =>
            genall (translateExpression(AppExp(LamExp(name, body), LamExp(IdnDef("x", UnknownType()), IfExp(EqualExp(AppExp(IdnUse("length"), IdnUse("x")), IntExp(3)), 
                                                                                                            AppExp(LamExp(IdnDef(a, UnknownType()), exp), AppExp(IdnUse("head"), AppExp(IdnUse("tail"), IdnUse("x")))), IntExp(999))))))
      

        // FIXME
        // handle:
        //    IfExp
        //    AppExp - "head" exp
        //           - "tail" exp
        //           - "length" exp
        //           - all other: exp exp
        //    ListExp
        //    LetExp

        case _ =>
            gen (IPrint ())
        }

        // Gather the expression's instructions and return them
        expInstrBuffer.result ()

    }

}
