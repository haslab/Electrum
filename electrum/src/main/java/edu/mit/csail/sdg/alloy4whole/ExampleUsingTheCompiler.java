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

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import edu.mit.csail.sdg.alloy4viz.VizGUI;

/** This class demonstrates how to access Alloy4 via the compiler methods. 
 * 
 * @modified [HASLab]
 * */

public final class ExampleUsingTheCompiler {

    /*
     * Execute every command in every file.
     *
     * This method parses every file, then execute every command.
     *
     * If there are syntax or type errors, it may throw
     * a ErrorSyntax or ErrorType or ErrorAPI or ErrorFatal exception.
     * You should catch them and display them,
     * and they may contain filename/line/column information.
     */
    public static void main(String[] args) throws Err {
        // The visualizer (We will initialize it to nonnull when we visualize an Alloy solution)
        VizGUI viz = null;

        A4Reporter rep = new A4Reporter() {
            
            @Override public void translate (String solver, String strat, int bitwidth, int maxseq, int skolemDepth, int symmetry) {
            	
            }
            
            @Override public void solve (int primaryVars, int totalVars, int clauses) {
            
            }
            
        };
        args = new String[] {"/Users/nmm/hotel_event.ele"};
        for(String filename:args) {

            Module world = CompUtil.parseEverything_fromFile(rep, null, filename);
            Sig en = world.getAllSigs().get(6);
            Sig ci = world.getAllSigs().get(7);
            Sig co = world.getAllSigs().get(8);

            // Choose some default options for how you want to execute the commands
            A4Options options = new A4Options();
            options.solver = A4Options.SatSolver.GlucoseJNI;
            options.originalFilename = filename;

            for (Command command: world.getAllCommands()) {
                // Execute the command

            	long now; float tot=0;
            	A4Solution ans = null;
            	
            	for (int i = 0; i<10; i++) {
	            	now = System.currentTimeMillis();
	                ans = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), command, options);
	                tot += System.currentTimeMillis()-now;
            	}
                System.out.println("base (l"+(ans.getLastState()+1)+"): "+tot/10/1000);
                
                A4Solution base = ans.next().next();
                
                base.writeXML("alloy_example_output.xml");
                new VizGUI(false, "alloy_example_output.xml", null);
                
                tot = 0;
            	for (int i = 0; i<10; i++) {
	                now = System.currentTimeMillis();
	                ans = base.next(en.prime().some(), 3);
	                tot+= System.currentTimeMillis()-now;
            	}
                System.out.println("entry at 4? "+ans.satisfiable()+(ans.satisfiable()?" (l"+(ans.getLastState()+1)+"): ":": ")+tot/10/1000);

                ans.writeXML("alloy_example_output.xml");
                new VizGUI(false, "alloy_example_output.xml", null);
                
                tot = 0;
            	for (int i = 0; i<10; i++) {
	                now = System.currentTimeMillis();
	                ans = base.next(ci.prime().some(), 3);
	                tot+= System.currentTimeMillis()-now;
            	}
                System.out.println("checkin at 4? "+ans.satisfiable()+(ans.satisfiable()?" (l"+(ans.getLastState()+1)+"): ":": ")+tot/10/1000);

                tot = 0;
            	for (int i = 0; i<10; i++) {
	                now = System.currentTimeMillis();
	                ans = base.next(co.prime().some(), 3);
	                tot+= System.currentTimeMillis()-now;
            	}
                System.out.println("checkout at 4? "+ans.satisfiable()+(ans.satisfiable()?" (l"+(ans.getLastState()+1)+"): ":": ")+tot/10/1000);


                
                tot = 0;
            	for (int i = 0; i<10; i++) {
	                now = System.currentTimeMillis();
	                ans = base.next(ci.prime().some(), 4);
	                tot+= System.currentTimeMillis()-now;
            	}
                System.out.println("checkin at 5? "+ans.satisfiable()+(ans.satisfiable()?" (l"+(ans.getLastState()+1)+"): ":": ")+tot/10/1000);

                tot = 0;
            	for (int i = 0; i<10; i++) {
	                now = System.currentTimeMillis();
	                ans = base.next(co.prime().some(), 4);
	                tot+= System.currentTimeMillis()-now;
            	}
                System.out.println("checkout at 5? "+ans.satisfiable()+(ans.satisfiable()?" (l"+(ans.getLastState()+1)+"): ":": ")+tot/10/1000);

                tot = 0;
            	for (int i = 0; i<10; i++) {
	                now = System.currentTimeMillis();
	                ans = base.next(en.prime().some(), 4);
	                tot+= System.currentTimeMillis()-now;
            	}
                System.out.println("entry at 5? "+ans.satisfiable()+(ans.satisfiable()?" (l"+(ans.getLastState()+1)+"): ":": ")+tot/10/1000);
                System.out.println("");

            	for (int i = 0; i<10; i++) {
	            	now = System.currentTimeMillis();
	                ans = base.next();
	                tot += System.currentTimeMillis()-now;
            	}
                System.out.println("base (l"+(ans.getLastState()+1)+"): "+tot/10/1000);
                base = ans.next();

                tot = 0;
            	for (int i = 0; i<10; i++) {
	                now = System.currentTimeMillis();
	                ans = base.next(ci.prime().some(), 3);
	                tot+= System.currentTimeMillis()-now;
            	}
                System.out.println("checkin at 4? "+ans.satisfiable()+(ans.satisfiable()?" (l"+(ans.getLastState()+1)+"): ":": ")+tot/10/1000);

                tot = 0;
            	for (int i = 0; i<10; i++) {
	                now = System.currentTimeMillis();
	                ans = base.next(co.prime().some(), 3);
	                tot+= System.currentTimeMillis()-now;
            	}
                System.out.println("checkout at 4? "+ans.satisfiable()+(ans.satisfiable()?" (l"+(ans.getLastState()+1)+"): ":": ")+tot/10/1000);

                tot = 0;
            	for (int i = 0; i<10; i++) {
	                now = System.currentTimeMillis();
	                ans = base.next(en.prime().some(), 3);
	                tot+= System.currentTimeMillis()-now;
            	}
                System.out.println("entry at 4? "+ans.satisfiable()+(ans.satisfiable()?" (l"+(ans.getLastState()+1)+"): ":": ")+tot/10/1000);

                
                tot = 0;
            	for (int i = 0; i<10; i++) {
	                now = System.currentTimeMillis();
	                ans = base.next(ci.prime().some(), 4);
	                tot+= System.currentTimeMillis()-now;
            	}
                System.out.println("checkin at 5? "+ans.satisfiable()+(ans.satisfiable()?" (l"+(ans.getLastState()+1)+"): ":": ")+tot/10/1000);

                tot = 0;
            	for (int i = 0; i<10; i++) {
	                now = System.currentTimeMillis();
	                ans = base.next(co.prime().some(), 4);
	                tot+= System.currentTimeMillis()-now;
            	}
                System.out.println("checkout at 5? "+ans.satisfiable()+(ans.satisfiable()?" (l"+(ans.getLastState()+1)+"): ":": ")+tot/10/1000);

                tot = 0;
            	for (int i = 0; i<10; i++) {
	                now = System.currentTimeMillis();
	                ans = base.next(en.prime().some(), 4);
	                tot+= System.currentTimeMillis()-now;
            	}
                System.out.println("entry at 5? "+ans.satisfiable()+(ans.satisfiable()?" (l"+(ans.getLastState()+1)+"): ":": ")+tot/10/1000);

                
//                if (ans.satisfiable()) {
//                    ans.writeXML("alloy_example_output.xml");
//                    if (viz==null) {
//                        viz = new VizGUI(false, "alloy_example_output.xml", null);
//                    } else {
//                        viz.loadXML("alloy_example_output.xml", true);
//                    }
//                }
            }
        }
    }
}
