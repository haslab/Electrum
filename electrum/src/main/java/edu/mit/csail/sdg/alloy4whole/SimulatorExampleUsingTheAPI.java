/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4whole;

import static edu.mit.csail.sdg.alloy4.A4Reporter.NOP;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.UNIV;

import java.util.Arrays;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Attr;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Decl;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.Func;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;

/** This class demonstrates how to access Alloy4 via the API. */

public final class SimulatorExampleUsingTheAPI {

    public static void main(String[] args) throws Err {

        // Chooses the Alloy4 options
        A4Options opt = new A4Options();
        opt.solver = A4Options.SatSolver.SAT4J;
        opt.originalFilename = "nop.tmp";

        // abstract sig A {}
//        PrimSig A = new PrimSig("A", Attr.ONE);

        // var sig A1 extends A {}
        PrimSig A1 = new PrimSig("A1", Attr.VARIABLE);

        // var sig A2 extends A {}
//        PrimSig B = new PrimSig("B", Attr.ONE);

        // var sig A2 extends A {}
        PrimSig B1 = new PrimSig("B1", Attr.VARIABLE);

        // A { f: B lone->lone B }
//        Expr f = A.addField("f", A1.lone_arrow_lone(A1));
        // Since (B lone->lone B) is not unary,  the default is "setOf",  meaning "f:set (B lone->lone B)"

        // A { g: B }
//        Expr g = A.addField("g", A2.setOf());
        // The line above is the same as:   A.addField(null, "g", B.oneOf())  since B is unary.
        // If you want "setOf", you need:   A.addField(null, "g", B.setOf())

        List<Sig> sigs = Arrays.asList(new Sig[]{A1, B1});

        // run { some A && atMostThree[B,B] } for 3 but 3 int, 3 seq
        Expr expr1 = (A1.equal(A1.prime())).not().always().and(B1.some()).and(B1.no().always().eventually());
        Command cmd1 = new Command(false, 2, 0, -1, 1, 10, expr1);
        A4Solution sol1 = TranslateAlloyToKodkod.execute_command(NOP, sigs, cmd1, opt);
        System.out.println("[Solution1]:");
        System.out.println(sol1.toString());

        A4Solution sol2 = sol1.nextState(2);
        System.out.println("[Solution2]:");
        System.out.println(sol2.toString());
    }
}
