/**
 * HasLang language execution tests.
 *
 * Copyright 2021, Anthony Sloane, Kym Haines, Macquarie University, All rights reserved.
 */

package haslang

import org.bitbucket.inkytonik.kiama.util.ParseTests
import org.junit.runner.RunWith
import org.scalatest.junit.JUnitRunner

/**
 * Tests that check that the translation works correctly.
 */
@RunWith(classOf[JUnitRunner])
class ExecTests extends ParseTests {

    import org.bitbucket.inkytonik.kiama.util.StringSource
    import org.bitbucket.inkytonik.kiama.util.StringEmitter
    import org.bitbucket.inkytonik.kiama.parsing.{Success,Failure,Error}

    import HasLangTree._
    import SECTree._

    val parsers = new SyntaxAnalysis (positions)
    import parsers._

    /**
     * Parse some test input and, if the parse succeeds with no input left,
     * return the program tree. If the parse fails, fail the test.
     */
    def parseProgram (str : String) : Program = {
        val posns = positions

        // Create a messaging module for semantic analysis
        /*
        val messaging = new Messaging with PositionStore {
                           override val positions = posns
                        }
        */

        parseAll (program, new StringSource(str)) match {
            case Success (r, in) =>
                if (!in.atEnd) fail ("input remaining at " + in.pos)
                r
            case f : Error =>
                fail ("parse error: " + f)
            case f : Failure =>
                fail ("parse failure: " + f)
        }
    }

    /**
     * Parse some test input, perform semantic analysis checks, expect no
     * semantic errors. Then translate into SEC machine code and run the code.
     * The value `expected` should be the output that we expect from this
     * run.
     */
    def execTest (str : String, expected : String) {
        val tree = parseProgram (str)
        /*
        val analysis = new SemanticAnalysis (new ExpTree (tree))
        import analysis._
        val messages = analysis.errors (tree)
        // println (messages)
        assert (messages.length === 0)
        */

        val instrs = Translator.translate (tree)
        // println (instrs)

        val emitter = new StringEmitter ()
        val machine = new SECMachine (emitter)

        machine.run (instrs) match {
            case _ : machine.State =>
                // Terminated correctly in some state
                assertResult (expected + "\n", "wrong execution output") (emitter.result ())
            case machine.FatalError (message) =>
                fail (message)
        }
    }

    // Translation tests that check the byte code that is produced.
    // Used to narrow down faults during marking...

    def translateTest (str: String, expected : Frame) {
        val tree = parseProgram(str)
        val instrs = Translator.translate(tree)

        assertResult (expected, "wrong translation output") (instrs)
    }

    test ("IF: a true less-than conditional expression evaluates to the correct result") {
        execTest ("""
            |if (1 < 2) then 15 else 0
            """.stripMargin,
            "15")
    }

    test ("a false less-than conditional expression evaluates to the correct result") {
        execTest ("""
            |if (4 < 2) then 15 else 0
            """.stripMargin,
            "0")
    }

    test ("translate if(true) then 3 else 4")
    {
        translateTest("if(true) then 3 else 4",
            List(IBool(true), IBranch(List(IInt(3)),List(IInt(4))), IPrint()))
    }

    test ("LIST: list []") {
        execTest ("""
            |[]
            """.stripMargin,
            "[]")
    }

    test ("list [4, 3, 7]") {
        execTest ("""
            |[4, 3, 7]
            """.stripMargin,
            "[4, 3, 7]")
    }

    test ("APP EXP: head [2, 1, 4]") {
        execTest ("""
            |head [2, 1, 4]
            """.stripMargin,
            "2")
    }

    test ("LET ONE DEF: a single def let evaluates to the correct result") {
        execTest ("""
            |let
            |   x :: Int = 1
            |in x
            |""".stripMargin,
            "1")
    }

    test ("a let with a calculation evaluates to the correct result") {
        execTest ("""
            |let
            |  x :: Int = 5
            |in x + 4
            |""".stripMargin,
            "9")
    }

    test ("translate let x :: Int = 3 in x + 4")
    {
        translateTest("let x :: Int = 3 in x + 4",
            List(IClosure("x",List(IVar("x"), IInt(4), IAdd(), IPopEnv())),
                 IInt(3), ICall(), IPrint()))
    }

    test ("LET ONE DEF FUN: a let with a single function definition evaluates to the correct result") {
        execTest ("""
            |let
            |  inc :: Int -> Int = \ a :: Int -> a + 1
            |in inc 1
            """.stripMargin,
            "2")
    }

    test ("a single function let evaluates to the correct result") {
        execTest ("""
            |let
            |  f :: Int -> Int = \ x :: Int -> x
            |in f
            """.stripMargin,
            "function of x")
    }

    test ("translate let f ... in f 4")
    {
        translateTest("let f :: Int -> Int = \\ x :: Int -> 2 * x in f 4",
            List(IClosure("f",List(IVar("f"), IInt(4), ICall(), IPopEnv())),
                 IClosure("x",List(IInt(2), IVar("x"), IMul(), IPopEnv())),
                 ICall(), IPrint()))
    }

    test ("LET MULT DEF: a multiple def let evaluates to the correct result (use first def)") {
        execTest ("""
            |let
            |   x :: Int = 1;
            |   y :: Int = 2
            |in x
            """.stripMargin,
            "1")
    }

    test ("a multiple def let evaluates to the correct result (use both defs)") {
        execTest ("""
            |let
            |  x :: Int = 1;
            |  y :: Int = 2
            |in x + y
            """.stripMargin,
            "3")
    }

    test ("LET MULT DEF FUN: a multiple function let evaluates to the correct result (use first fun)") {
        execTest ("""
            |let
            |  f :: Int -> Int = \ x :: Int -> x + 1;
            |  g :: Int -> Int = \ y :: Int -> y * 2
            |in f 4
            """.stripMargin,
            "5")
    }

    test ("translate let f ... ; g ... in (f 4) + (g 4)")
    {
        translateTest("let f :: Int -> Int = \\ x :: Int -> x+1; g :: Int -> Int = \\ y :: Int -> y*2 in (f 4) + (g 4)",
            List(IClosure("f",List(IClosure("g",List(IVar("f"), IInt(4),
                ICall(), IVar("g"), IInt(4), ICall(), IAdd(), IPopEnv())),
                IClosure("y",List(IVar("y"), IInt(2), IMul(), IPopEnv())),
                ICall(), IPopEnv())),
                IClosure("x",List(IVar("x"), IInt(1), IAdd(), IPopEnv())),
                ICall(), IPrint()))
    }

    test ("LET NESTED ONE DEF: simple let in let") {
        execTest ("""
            |let
            |  c :: Int = 7
            |in let
            |     d :: Int = 4
            |   in
            |     c + d
            """.stripMargin,
            "11")
    }

    test ("LET NESTED ONE DEF FUN: backward reference is evaluated correctly (same group)") {
        execTest ("""
            |let
            |  g :: Int -> Int = \ x :: Int -> x * 2
            |in let h :: Int -> Int = \ y :: Int -> g y
            |   in h 3
            """.stripMargin,
            "6")
    }

    test ("a function using a val is evaluated correctly (1)") {
        execTest ("""
            |let
            |  x :: Int = 1
            |in let f :: Int -> Int = \ y :: Int -> x
            |   in f 4
            """.stripMargin,
            "1")
    }

    test ("a function using a val is evaluated correctly (2)") {
        execTest ("""
            |let
            |  x :: Int = 7
            |in let  f :: Int -> Int = \ y :: Int -> y + x
            |   in f 4
            """.stripMargin,
            "11")
    }

    test ("LET COMPLEX: a multiple function let with vals before and after evaluates to the correct result (use both funs)") {
        execTest ("""
            |let
            |  w :: Int = 7;
            |  f :: Int -> Int = \ x :: Int -> x + 1;
            |  g :: Int -> Int = \ y :: Int -> y * 2
            |in let  z :: Int = f w
            |   in (f z) + (g 4)
            """.stripMargin,
            "17")
    }

    test ("call with call argument is evaluated correctly") {
        execTest ("""
            |let
            |  inc :: Int -> Int = \ x :: Int -> x + 1;
            |  dec :: Int -> Int = \ x :: Int -> x - 1
            |in inc (dec 4)
            """.stripMargin,
            "4")
    }

    test ("translate let w = 7; f ... ; g ... ; z = f w in (f z) + (g 4)")
    {
        translateTest(
            "let w :: Int = 7; f :: Int -> Int = \\ x :: Int -> x+1; g :: Int -> Int = \\ y ::Int -> y*2; z :: Int = f w in (f z) + (g 4)",
            List(IClosure("w",List(IClosure("f",List(IClosure("g",
                List(IClosure("z", List(IVar("f"), IVar("z"), ICall(),
                IVar("g"), IInt(4), ICall(), IAdd(), IPopEnv())), IVar("f"),
                IVar("w"), ICall(), ICall(), IPopEnv())),
                IClosure("y",List(IVar("y"), IInt(2), IMul(),
                IPopEnv())), ICall(), IPopEnv())), IClosure("x",List(IVar("x"),
                IInt(1), IAdd(), IPopEnv())), ICall(), IPopEnv())), IInt(7),
                ICall(), IPrint()))
    }

    test ("SIMPLE PATTERNS: translate foo 3 = 2")
    {
        translateTest("""
                |let
                |  foo :: Int -> Int
                |  foo 3 = 2
                |in
                |  foo 3
                """.stripMargin,
            List(IClosure("foo",List(IVar("foo"), IInt(3), ICall(), IPopEnv())),
                 IClosure("x",List(IVar("x"), IInt(3), IEqual(),
                 IBranch(List(IInt(2)),List(IInt(999))), IPopEnv())),
                 ICall(), IPrint()))
    }

    test ("execute foo 3 = 2 with 3")
    {
        execTest("""
                |let
                |  foo :: Int -> Int
                |  foo 3 = 2
                |in
                |  foo 3
                """.stripMargin,
                "2")
    }

    test ("execute foo 3 = 2 with 4")
    {
        execTest("""
                |let
                |  foo :: Int -> Int
                |  foo 3 = 2
                |in
                |  foo 4
                """.stripMargin,
                "999")
    }

    test ("execute foo false = 6")
    {
        execTest("""
                |let
                |  foo :: Bool -> Int
                |  foo false = 6
                |in
                |  1000 * foo false + foo true
                """.stripMargin,
                "6999")
    }

    test ("translate foo n = 2 * n")
    {
        translateTest("""
                |let
                |  foo :: Int -> Int
                |  foo n = 2 * n
                |in
                |  foo 3
                """.stripMargin,
            List(IClosure("foo",List(IVar("foo"), IInt(3), ICall(), IPopEnv())),
                 IClosure("x",List(IClosure("n",List(IInt(2), IVar("n"),
                 IMul(), IPopEnv())), IVar("x"), ICall(), IPopEnv())),
                 ICall(), IPrint()))
    }

    test ("execute foo n = 2 * n with 3")
    {
        execTest("""
                |let
                |  foo :: Int -> Int
                |  foo n = 2 * n
                |in
                |  foo 3
                """.stripMargin,
                "6")
    }

    test ("translate foo _ = 7")
    {
        translateTest("""
                |let
                |  foo :: Int -> Int
                |  foo _ = 7
                |in
                |  foo 3
                """.stripMargin,
            List(IClosure("foo",List(IVar("foo"), IInt(3), ICall(), IPopEnv())),
                 IClosure("x",List(IInt(7), IPopEnv())), ICall(), IPrint()))
    }

    test ("execute foo _ = 7 with 3")
    {
        execTest("""
                |let
                |  foo :: Int -> Int
                |  foo _ = 7
                |in
                |  foo 3
                """.stripMargin,
                "7")
    }

    test ("FACTORIAL: translate fac")
    {
        translateTest("""
                |let
                |  fac :: Int -> Int
                |  fac 0 = 1.
                |  fac n = n * fac (n - 1)
                |in
                |  fac 3
                """.stripMargin,
            List(IClosure("fac",List(IVar("fac"), IInt(3), ICall(), IPopEnv())),
                 IClosure("x",List(IVar("x"), IInt(0), IEqual(),
                 IBranch(List(IInt(1)),List(IClosure("n",List(IVar("n"),
                 IVar("fac"), IVar("n"), IInt(1), ISub(), ICall(), IMul(),
                 IPopEnv())), IVar("x"), ICall())), IPopEnv())),
                 ICall(), IPrint()))
    }

    test ("execute fac with 3")
    {
        execTest("""
                |let
                |  fac :: Int -> Int
                |  fac 0 = 1.
                |  fac n = n * fac (n - 1)
                |in
                |  fac 3
                """.stripMargin,
                "6")
    }

    test ("LIST PATTERNS: execute foo []")
    {
        execTest("""
                |let
                |  foo :: [Int] -> Int
                |  foo [] = 5
                |in
                |  1000 * foo [] + foo [3]
                """.stripMargin,
                "5999")
    }

    test ("execute foo [8]")
    {
        execTest("""
                |let
                |  foo :: [Int] -> Int
                |  foo [8] = 4
                |in
                |  1000 * foo [8] + foo [3]
                """.stripMargin,
                "4999")
    }

    test ("execute foo [k]")
    {
        execTest("""
                |let
                |  foo :: [Int] -> Int
                |  foo [k] = 3 * k + 1
                |in
                |  1000 * foo [2] + foo [3, 4]
                """.stripMargin,
                "7999")
    }

    test ("execute foo [_, u]")
    {
        execTest("""
                |let
                |  foo :: [Int] -> Int
                |  foo [_, u] = u + 2
                |in
                |  1000 * foo [2, 4] + foo [3, 4, 5]
                """.stripMargin,
                "6999")
    }

    test ("execute foo [r, 1, s]")
    {
        execTest("""
                |let
                |  foo :: [Int] -> Int
                |  foo [r, 1, s] = 2 * r + s
                |in
                |  1000 * foo [3, 1, 2] + foo [3, 4, 5]
                """.stripMargin,
                "8999")
    }

    test ("CONS PATTERNS: execute foo 3:_")
    {
        execTest("""
                |let
                |  foo :: [Int] -> Int
                |  foo 3:_ = 2
                |in
                |  1000 * foo [3, 4] + foo [5]
                """.stripMargin,
                "2999")
    }

    test ("execute foo g:h")
    {
        execTest("""
                |let
                |  foo :: [Int] -> Int
                |  foo g:h = g : 4 : h
                |in
                |  foo [3, 5, 6]
                """.stripMargin,
                "[3, 4, 5, 6]")
    }

    test ("execute len [7, 4, 7]")
    {
        execTest("""
                |let
                |  len :: Int -> Int
                |  len [] = 0.
                |  len _:t = 1 + len t
                |in
                |  len [7, 4, 7]
                """.stripMargin,
                "3")
    }

    //==================================================================

    // FIXME: more tests here...

}

