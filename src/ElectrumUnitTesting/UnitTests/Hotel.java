package ElectrumUnitTesting.UnitTests;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;
import kodkod.engine.Solution;
import org.junit.Test;

import java.io.IOException;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertSame;


public class Hotel {

    private static SimpleReporter rep;
    private static A4Options opt;
    private static Module cp;
    private static String path;

    public Hotel() throws IOException, Err {
        opt = new A4Options();
        opt.noOverflow = true;
        opt.skolemDepth = 1;
        rep = new SimpleReporter();
        path = "./src/ElectrumUnitTesting/models/ring.ele";
        cp = CompUtil.parseEverything_fromFile(rep, null, path);

    }

    /*Badliveness check ( the expected outcome is unsatisfiable)*/
    @Test
    public final void BadSafety() throws IOException, Err {
        opt.maxTraceLength = 10;
        A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, cp.getAllReachableSigs(), cp.getAllCommands().get(0), opt);
        assertEquals(ans.solvingOutcome, Solution.Outcome.SATISFIABLE);
    }


    /*GoodSafety check ( the expected outcome is unsatisfiable)*/
    @Test
    public final void GoodSafety() throws IOException, Err {
        opt.maxTraceLength = 10;
        A4Solution ans = TranslateAlloyToKodkod.execute_command(rep, cp.getAllReachableSigs(), cp.getAllCommands().get(1), opt);
        assertEquals(ans.solvingOutcome, Solution.Outcome.UNSATISFIABLE);
    }


    private static final class SimpleReporter
            extends A4Reporter {
        private final StringBuilder sb = new StringBuilder();
        private final List<ErrorWarning> warnings = new ArrayList<ErrorWarning>();
        private final RandomAccessFile os = new RandomAccessFile("alloy.tmp", "rw");
        public final List<Long> times = new ArrayList<Long>();

        public SimpleReporter() throws IOException {
            this.os.setLength(0);
        }

        public void flush() throws IOException {
            if (this.sb.length() > 65536) {
                this.os.write(this.sb.toString().getBytes("UTF-8"));
                this.sb.delete(0, this.sb.length());
            }
        }

        public void close() throws IOException {
            if (this.sb.length() > 0) {
                this.os.write(this.sb.toString().getBytes("UTF-8"));
                this.sb.delete(0, this.sb.length());
            }
            this.os.close();
        }

        @Override
        public void debug(String msg) {
            this.sb.append(msg);
        }

        @Override
        public void parse(String msg) {
            this.sb.append(msg);
        }

        @Override
        public void typecheck(String msg) {
            this.sb.append(msg);
        }

        @Override
        public void warning(ErrorWarning msg) {
            this.warnings.add(msg);
        }

        @Override
        public void scope(String msg) {
            this.sb.append("   ");
            this.sb.append(msg);
        }

        @Override
        public void bound(String msg) {
            this.sb.append("   ");
            this.sb.append(msg);
        }

        @Override
        public void translate(String solver, int bitwidth, int maxseq, int skolemDepth, int symmetry) {
            this.sb.append("   Solver=" + solver + " Bitwidth=" + bitwidth + " MaxSeq=" + maxseq + " Symmetry=" + (symmetry > 0 ? new StringBuilder().append(symmetry).toString() : "OFF") + "\n");
        }

        @Override
        public void solve(int primaryVars, int totalVars, int clauses) {
            this.sb.append("   " + totalVars + " vars. " + primaryVars + " primary vars. " + clauses + " clauses. 12345ms.\n");
        }

        @Override
        public void resultCNF(String filename) {
        }

        @Override
        public void resultSAT(Object command, long solvingTime, Object solution) {
            if (!(command instanceof Command)) {
                return;
            }
            Command cmd = (Command) command;
            this.sb.append(cmd.check ? "   Counterexample found. " : "   Instance found. ");
            if (cmd.check) {
                this.sb.append("Assertion is invalid");
            } else {
                this.sb.append("Predicate is consistent");
            }
            if (cmd.expects == 0) {
                this.sb.append(", contrary to expectation");
            } else if (cmd.expects == 1) {
                this.sb.append(", as expected");
            }
            this.sb.append(". " + solvingTime + "ms.\n\n");
        }

        @Override
        public void resultUNSAT(Object command, long solvingTime, Object solution) {
            if (!(command instanceof Command)) {
                return;
            }
            Command cmd = (Command) command;
            this.sb.append(cmd.check ? "   No counterexample found." : "   No instance found.");
            if (cmd.check) {
                this.sb.append(" Assertion may be valid");
            } else {
                this.sb.append(" Predicate may be inconsistent");
            }
            if (cmd.expects == 1) {
                this.sb.append(", contrary to expectation");
            } else if (cmd.expects == 0) {
                this.sb.append(", as expected");
            }
            this.sb.append(". " + solvingTime + "ms.\n\n");
        }
    }
}
