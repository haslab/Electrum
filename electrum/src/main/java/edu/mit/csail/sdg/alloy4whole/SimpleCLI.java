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

import java.io.IOException;
import java.util.List;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.OptionGroup;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;

public final class SimpleCLI {

    private static final class SimpleReporter extends A4Reporter {
        private Logger LOGGER = LoggerFactory.getLogger(A4Reporter.class);

        public SimpleReporter() throws IOException { }

        @Override public void debug(String msg) { 
        		if (System.getProperty("debug","no").equals("yes"))
        			LOGGER.debug(msg); 
        	}

        @Override public void parse(String msg) { debug(msg); }

        @Override public void typecheck(String msg) { debug(msg); }

        public void info(String msg) { LOGGER.info(msg); }

        @Override public void warning(ErrorWarning msg) { LOGGER.warn(msg.msg); }

        @Override public void scope(String msg) { debug(msg); }

        @Override public void bound(String msg) { debug(msg); }

        @Override public void translate(String solver, int bitwidth, int maxseq, int skolemDepth, int symmetry) {
        		debug("Solver="+solver+" Bitwidth="+bitwidth+" MaxSeq="+maxseq+" Symmetry="+(symmetry>0 ? (""+symmetry) : "OFF")+"\n");
        }

        @Override public void solve(int primaryVars, int totalVars, int clauses) {
            debug(totalVars+" vars. "+primaryVars+" primary vars. "+clauses+" clauses.\n");
        }

        @Override public void resultCNF(String filename) {}

        @Override public void resultSAT(Object command, long solvingTime, Object solution) {
            if (!(command instanceof Command)) return;
            Command cmd = (Command)command;
            StringBuilder sb = new StringBuilder();
            sb.append(cmd.check ? "   Counterexample found. " : "   Instance found. ");
            if (cmd.check) sb.append("Assertion is invalid"); else sb.append("Predicate is consistent");
            if (cmd.expects==0) sb.append(", contrary to expectation"); else if (cmd.expects==1) sb.append(", as expected");
            sb.append(". "+solvingTime+"ms.\n\n");
            info(sb.toString());
        }

        @Override public void resultUNSAT(Object command, long solvingTime, Object solution) {
            if (!(command instanceof Command)) return;
            Command cmd = (Command)command;
            StringBuilder sb = new StringBuilder();
            sb.append(cmd.check ? "   No counterexample found." : "   No instance found.");
            if (cmd.check) sb.append(" Assertion may be valid"); else sb.append(" Predicate may be inconsistent");
            if (cmd.expects==1) sb.append(", contrary to expectation"); else if (cmd.expects==0) sb.append(", as expected");
            sb.append(". "+solvingTime+"ms.\n\n");
            info(sb.toString());
        }
    }

    private SimpleCLI() { }

    private static Options options() {
    		Options options = new Options();

    		options.addOption(Option.builder("d")
    				.longOpt("decomposed")
    				.hasArg(true)
    				.argName("threads")
    				.optionalArg(true)
    				.required(false)
    				.desc("run in decomposed mode").build());
    		
    		options.addOption(Option.builder("c")
    				.longOpt("command")
    				.hasArg(true)
    				.argName("command")
    				.optionalArg(false)
    				.required(false)
    				.desc("select command").build());
    		
    		options.addOption(Option.builder("v")
    				.longOpt("verbose")
    				.hasArg(false)
    				.required(false)
    				.desc("run in debug mode").build());
    		
    		OptionGroup g = new OptionGroup();
    		g.addOption(Option.builder("x").longOpt("nuXmv").hasArg(false).desc("select nuXmv unbounded solver").build());
    		g.addOption(Option.builder("m").longOpt("miniSAT").hasArg(false).desc("select miniSAT bounded solver").build());
    		g.addOption(Option.builder("n").longOpt("NuSMV").hasArg(false).desc("select NuSMV unbounded solver").build());
    		g.addOption(Option.builder("s").longOpt("SAT4J").hasArg(false).desc("select SAT4J bounded solver").build());
    		g.setRequired(true);
    		
    		options.addOptionGroup(g);

    		return options;
    }
    
    public static void main(String[] args) throws Exception {
    		CommandLine cmd = null;	
    		try {
    			CommandLineParser parser = new DefaultParser();
    			cmd = parser.parse(options(), args, true);
    		} catch(ParseException exp) {
    	        System.err.println( "Parsing failed.  Reason: " + exp.getMessage() );
    	        HelpFormatter formatter = new HelpFormatter();
    	        formatter.printHelp("electrum [options] [FILE]",options());
    	        return;
    	    }
    	
    		if (cmd.hasOption("v")) System.setProperty("debug","yes");
    		
		final SimpleReporter rep = new SimpleReporter();
		String filename = args[args.length - 1];
		try {
			rep.info("Parsing " + filename + ".\n");
			Module world = CompUtil.parseEverything_fromFile(rep, null, filename);
			List<Command> cmds = world.getAllCommands();
			A4Options options = new A4Options();
			options.originalFilename = filename;
			options.solver = A4Options.SatSolver.MiniSatJNI;
			if (cmd.hasOption("SAT4J"))
				options.solver = A4Options.SatSolver.SAT4J;
			else if (cmd.hasOption("NuSMV"))
				options.solver = A4Options.SatSolver.ElectrodS;
			else if (cmd.hasOption("nuXmv"))
				options.solver = A4Options.SatSolver.ElectrodX;

			if (cmd.hasOption("decomposed"))
				if (cmd.getOptionValue("decomposed") != null)
					options.decomposed = Integer.valueOf(cmd.getOptionValue("decomposed"));
				else
					options.decomposed = 1;
			else
				options.decomposed = 0;
			int i0=0, i1=cmds.size();
			if (cmd.hasOption("command")) {
				i0 = Integer.valueOf(cmd.getOptionValue("command"));
				i1 = i0+1;
			} else {
				rep.info("Running all commands.");
			}
			for (int i = i0; i < i1; i++) {
				Command c = cmds.get(i);
				rep.info("Executing \"" + c + "\"\n");
				options.skolemDepth = 2;
				long time = System.currentTimeMillis();
				A4Solution s = TranslateAlloyToKodkod.execute_commandFromBook(rep, world.getAllReachableSigs(), c,
						options);
				time = System.currentTimeMillis() - time;
			}
		} catch (Throwable ex) {
			rep.info("An error occurred.");
			rep.debug("\n\nException: " + ex);
		}
	}
}
