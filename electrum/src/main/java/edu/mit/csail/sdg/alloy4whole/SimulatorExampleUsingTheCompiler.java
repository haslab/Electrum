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
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import edu.mit.csail.sdg.alloy4viz.VizGUI;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Evaluator;
import kodkod.instance.Instance;
import kodkod.instance.TemporalInstance;
import kodkod.instance.TupleSet;

/** This class demonstrates how to access Alloy4 via the compiler methods. 
 * 
 * @modified [HASLab]
 * */

public final class SimulatorExampleUsingTheCompiler {

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
        
        String[] events = new String[] {"_In","_Out","_Reentry","_Entry"};
        
        args = new String[] {"/Users/nmm/Downloads/hotel-actions.ele"};
        for(String filename:args) {

            Module world = CompUtil.parseEverything_fromFile(rep, null, filename);

            // assumes all commands same time
            int mtime = world.getAllCommands().get(0).maxtime;
            
            Object[][][] results_1 = new Object[world.getAllCommands().size()][mtime][events.length+2];
            Long[] results_2 = new Long[world.getAllCommands().size()];
            TemporalInstance[] results_3 = new TemporalInstance[world.getAllCommands().size()];
            

            // Choose some default options for how you want to execute the commands
            A4Options options = new A4Options();
            options.solver = A4Options.SatSolver.GlucoseJNI;
            options.originalFilename = filename;
            int tries = 10;
            
            for (int i = 0; i < tries; i++) {
	            for (int cmd_i = 0; cmd_i < world.getAllCommands().size(); cmd_i++) {
	                // Execute the command
	
	            	A4Solution ans = null;
	            	
	            	long now = System.currentTimeMillis();
	                ans = TranslateAlloyToKodkod.execute_command(rep, world.getAllReachableSigs(), world.getAllCommands().get(cmd_i), options);
	                long time = System.currentTimeMillis() - now;
	                
	                results_2[cmd_i] = (long) (results_2[cmd_i] == null?(long) 0:results_2[cmd_i]) + time;
	                results_3[cmd_i] = (TemporalInstance) ans.debugExtractKInstance();
	                
	                for (int stp_i = 0; stp_i < mtime; stp_i++) {
	                	
		            	now = System.currentTimeMillis();
		            	int act_i;
		            	for (act_i = 0; act_i < events.length; act_i++) {
			            	results_1[cmd_i][stp_i][act_i] = ans.hasNext(stp_i, events[act_i]);
		            	}
		                time = System.currentTimeMillis() - now;
		                Relation ev = results_3[cmd_i].state(0).findRelationByName("this/_E._event");
		                results_1[cmd_i][stp_i][act_i++] = new Evaluator((TemporalInstance) results_3[cmd_i]).evaluate(ev,stp_i);
		                results_1[cmd_i][stp_i][act_i] = (long) (results_1[cmd_i][stp_i][act_i] == null?(long) 0:results_1[cmd_i][stp_i][act_i]) + time;
	                }
	                
	
	//                ans.writeXML("alloy_example_output.xml");
	//                new VizGUI(false, "alloy_example_output.xml", null);
	                
	            }
            }
            
            System.out.print("CMD\tExec\tConfig\t");
            for (int stp_i = 0; stp_i < mtime; stp_i++) {
            	for (int act_i = 0; act_i < events.length; act_i++) {
            		System.out.print(events[act_i]+"?\t");
            	}
        		System.out.print("Act\t");
        		System.out.print("Sum\t");
            }
        	System.out.println();
            
            for (int cmd_i = 0; cmd_i < world.getAllCommands().size(); cmd_i++) {
            	System.out.print(world.getAllCommands().get(cmd_i).toString()+"\t");
            	System.out.print(((long) results_2[cmd_i]/tries) + "\t");
            	for (Relation r : results_3[cmd_i].state(0).relations())
            		if (r.isVariable())
            			System.out.print(results_3[cmd_i].state(0).relationTuples() + " ");
            	System.out.print("\t");
                for (int stp_i = 0; stp_i < world.getAllCommands().get(cmd_i).maxtime; stp_i++) {
	            	int act_i;
                	for (act_i = 0; act_i < events.length; act_i++) {
	            		System.out.print(results_1[cmd_i][stp_i][act_i] + "\t");
	            	}
            		System.out.print((results_1[cmd_i][stp_i][act_i++]) + "\t");
            		System.out.print(((long) results_1[cmd_i][stp_i][act_i]/tries) + "\t");
                }
            	System.out.println();
            }
        }
    }
}

