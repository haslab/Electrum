package kodkod_examples;


import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.CommandScope;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateTAlloyToInit;

public final class BatchExamples {
	
	private static int min_n = 3;
	private static int max_n = 3;
	private static int min_t = 20;
	private static int max_t = 20;
	private final static int tries = 5;
	
	private final static String hotel = "/Users/nmm/Documents/Work/Projects/Onera/svn/CaseStudies/BookExamples/HotelLocking/Hotel.ele";
	private final static String hotel_fix = "/Users/nmm/Documents/Work/Projects/Onera/svn/CaseStudies/BookExamples/HotelLocking/Hotel_fixed_config.ele";
	private final static String span = "/Users/nmm/Documents/Work/Projects/Onera/svn/CaseStudies/SpanTree/span_tree.ele";
	private final static String ring = "/Users/nmm/Documents/Work/Projects/Onera/svn/CaseStudies/BookExamples/RingElection/election.ele";
	private final static String firewire = "/Users/nmm/Documents/Work/Projects/Onera/svn/Articles/ICSE2016/Examples/firewire.ele";
	private final static String android = "/Users/nmm/Documents/Work/Projects/Onera/svn/CaseStudies/AndroidPermissions/android-permission_simple.ele";
	
	private static Map<Sig,Integer> scopesigs = new HashMap<Sig,Integer>();

	private static SimpleReporter rep;
    private static A4Options opt;
    private static Module cp;
    
    private static String path;
    
	public static void main(String[] args) throws Exception {
		
				
        opt = new A4Options();
        opt.solver = A4Options.SatSolver.MiniSatJNI;
        opt.noOverflow = true;
        opt.skolemDepth = 1;
        // timeout??
        
//		opt.symmetry = 0;
//		cp = CompUtil.parseEverything_fromFile(rep, null, "/Users/nmm/Desktop/firewire_init.als");
//		A4Solution ai = TranslateAlloyToKodkod.execute_commandFromBook(rep, cp.getAllReachableSigs(), cp.getAllCommands().get(0), opt);
//		int cc = 0;
//		while (ai.satisfiable()) {
//        	cc++;
//			System.out.println(ai);
//			System.out.println(cc);
//        	ai = ai.next();
//        }

		
        rep = new SimpleReporter();
		path = ring;
		cp = CompUtil.parseEverything_fromFile(rep, null, path);
		
		goInit();

		// warm up
		TranslateTAlloyToAlloy tt = new TranslateTAlloyToAlloy(rep, cp.getAllCommands().get(0), cp.getAllReachableSigs());
		Command x = tt.untemp();
		for (int i =0; i<10; i++)
			TranslateAlloyToKodkod.execute_commandFromBook(rep, tt.new_sigs.values(), x, opt);

		go(2);
//		go(3);
		
//		min_n = 5;
//		max_n = 5;
//		min_t = 1;
//		max_t = 30;
//		
//		go(0);

		return;
	}

	private static List<CommandScope> updateScopes(int n) throws ErrorSyntax {
		List<CommandScope> css = new ArrayList<CommandScope>();
		for (Sig s : cp.getAllSigs()) {
			if (path.equals(firewire)) {
				if (s.label.equals("this/Node"))
					css.add(new CommandScope(s, false, n));
				else if (s.label.equals("this/Link"))
					css.add(new CommandScope(s, false, n*2));
				else if (s.label.equals("this/Msg"))
					css.add(new CommandScope(s, false, 2));
				else if (s.label.equals("this/Queue"))
					css.add(new CommandScope(s, false, 3));
			} else	if (path.equals(hotel)) {
				if (s.label.equals("this/Room"))
					css.add(new CommandScope(s, false, n));
				else if (s.label.equals("this/Guest"))
					css.add(new CommandScope(s, false, n));
				else if (s.label.equals("this/Key"))
					css.add(new CommandScope(s, false, n));
			} else	if (path.equals(span)) {
				if (s.label.equals("this/Process"))
					css.add(new CommandScope(s, false, n));
				else if (s.label.equals("this/Lvl"))
					css.add(new CommandScope(s, false, n));
			} else	if (path.equals(ring)) {
				if (s.label.equals("this/Process"))
					css.add(new CommandScope(s, false, n));
				else if (s.label.equals("this/Id"))
					css.add(new CommandScope(s, false, n));
			} else	if (path.equals(android)) {
				if (s.label.equals("this/Application"))
					css.add(new CommandScope(s, false, n-2));
				else if (s.label.equals("this/Component"))
					css.add(new CommandScope(s, false, n-2));
				else if (s.label.equals("this/Permission"))
					css.add(new CommandScope(s, false, n-1));
				else if (s.label.equals("this/PermName"))
					css.add(new CommandScope(s, false, n));
				else if (s.label.equals("this/URI"))
					css.add(new CommandScope(s, false, n));
			}			

		}
//		System.out.println(css);

		return css;
	}

	private static void go (int g) throws Exception {
		rep.times.clear();

		Command c = cp.getAllCommands().get(g);

		for (int t = min_t; t<=max_t; t++) {
//			System.out.print("t"+t);
			for (int n = min_n; n<=max_n; n++) {
				System.out.print(t+"\t"+n+ "\t");
				for (int k = 0; k<tries; k++) {
					List<CommandScope> css = updateScopes(n);
					Command nc = new Command(c.pos, c.label, c.check, 0, c.bitwidth, c.maxseq, t, false, c.expects, css, c.additionalExactScopes, c.formula, null);

					TranslateTAlloyToAlloy tt = new TranslateTAlloyToAlloy(rep, nc, cp.getAllReachableSigs());
					Command x = tt.untemp();
					//	        System.out.println("OLD: "+c.scope);
					//	        System.out.println("NEW: "+x.scope);

					A4Solution sol = TranslateAlloyToKodkod.execute_commandFromBook(rep, tt.new_sigs.values(), x, opt);
//					System.out.print(sol.toString());
					//	        System.out.println(ai.toString());
					System.out.print(rep.times.get(rep.times.size()-1)+"\t");
				}
				System.out.print("\n");

			}
		}
//		System.out.println(rep.times.size()+"");
//		System.out.println(rep.times+"");
//		for (int t = min_t; t<=max_t; t++)
//			for (int n = min_n; n<=max_n; n++) {
//				System.out.print(+t+"\t"+n+ "\t");
//				for (int k = 0; k<tries; k++)
//					System.out.print(rep.times.get((t-min_t)*(max_n-min_n+1)*tries+(n-min_n)*tries+k)+"\t");
//				System.out.print("\n");
//			}
	}
	
	private static void goInit() throws Exception {
		Command c = cp.getAllCommands().get(0);
		opt.symmetry = 20;
		for (int n = min_n; n<=max_n; n++) {
			System.out.print(n+ "\t");
				List<CommandScope> css = updateScopes(n);
				Command nc = new Command(c.pos, c.label, c.check, 0, c.bitwidth, c.maxseq, -1, false, c.expects, css, c.additionalExactScopes, c.formula, null);


				TranslateTAlloyToInit t = new TranslateTAlloyToInit(rep, nc,cp.getAllReachableSigs());
				Command x = t.untemp();
//				for (Sig s : cp.getAllReachableSigs())
//					System.out.print(s+": "+s.getFieldDecls());

				A4Solution ai=TranslateAlloyToKodkod.execute_commandFromBook(rep, t.old_sigs, x, opt);
		        int cc = 0;
		        while (ai.satisfiable()) {
		        	cc++;
//					System.out.println(ai);
					System.out.println(cc);
		        	ai = ai.next();
		        }
		    	System.out.print(cc);
			System.out.print("\n");

		}


	}
	
	 private static final class SimpleReporter extends A4Reporter {

	        private final StringBuilder sb = new StringBuilder();
	        
	        private final List<ErrorWarning> warnings = new ArrayList<ErrorWarning>();

	        private final RandomAccessFile os;

	        public final List<Long> times = new ArrayList<Long>();
	        
	        public SimpleReporter() throws IOException {
	            os = new RandomAccessFile("alloy.tmp","rw");
	            os.setLength(0);
	        }

	        public void flush() throws IOException {
	            if (sb.length()>65536) {
	                os.write(sb.toString().getBytes("UTF-8"));
	                sb.delete(0, sb.length());
	            }
	        }

	        public void close() throws IOException {
	            if (sb.length()>0) {
	                os.write(sb.toString().getBytes("UTF-8"));
	                sb.delete(0, sb.length());
	            }
	            os.close();
	        }

	        @Override public void debug(String msg) { 
	        	sb.append(msg); 
//	        	System.out.println(msg); 
	        	}

	        @Override public void parse(String msg) { sb.append(msg); }

	        @Override public void typecheck(String msg) { sb.append(msg); }

	        @Override public void warning(ErrorWarning msg) { warnings.add(msg); }

	        @Override public void scope(String msg) { sb.append("   "); sb.append(msg); }

	        @Override public void bound(String msg) { sb.append("   "); sb.append(msg); }

	        @Override public void translate(String solver, int bitwidth, int maxseq, int skolemDepth, int symmetry) {
	            sb.append("   Solver="+solver+" Bitwidth="+bitwidth+" MaxSeq="+maxseq+" Symmetry="+(symmetry>0 ? (""+symmetry) : "OFF")+"\n");
	        }

	        @Override public void solve(int primaryVars, int totalVars, int clauses) {
	            sb.append("   "+totalVars+" vars. "+primaryVars+" primary vars. "+clauses+" clauses. 12345ms.\n");
	        }

	        @Override public void resultCNF(String filename) {}

	        @Override public void resultSAT(Object command, long solvingTime, Object solution) {
	            if (!(command instanceof Command)) return;
	            Command cmd = (Command)command;
	            sb.append(cmd.check ? "   Counterexample found. " : "   Instance found. ");
	            if (cmd.check) sb.append("Assertion is invalid"); else sb.append("Predicate is consistent");
	            if (cmd.expects==0) sb.append(", contrary to expectation"); else if (cmd.expects==1) sb.append(", as expected");
	            sb.append(". "+solvingTime+"ms.\n\n");
	        }

	        @Override public void resultUNSAT(Object command, long solvingTime, Object solution) {
	            if (!(command instanceof Command)) return;
	            Command cmd = (Command)command;
	            sb.append(cmd.check ? "   No counterexample found." : "   No instance found.");
	            if (cmd.check) sb.append(" Assertion may be valid"); else sb.append(" Predicate may be inconsistent");
	            if (cmd.expects==1) sb.append(", contrary to expectation"); else if (cmd.expects==0) sb.append(", as expected");
	            sb.append(". "+solvingTime+"ms.\n\n");
	        }
	        
	        public void resultT(long solvingTime) {
	            times.add(solvingTime);
	        }
	        
	    }
	
}
