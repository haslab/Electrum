/* 
 * Kodkod -- Copyright (c) 2005-present, Emina Torlak
 * Pardinus -- Copyright (c) 2014-present, Nuno Macedo
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */
package kodkod.engine.decomp;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;

import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;

/**
 * A concretization of a decomposed problem executor designed to retrieve the
 * stats of a problem. Will not terminate once a SAT solution is found, but
 * rather when every integrated problem has terminated.
 * 
 * @author nmm
 */
public class StatsExecutor extends DProblemExecutor {


	/** the queue of solvers to be launched */
	private final List<DProblem> problem_queue = new ArrayList<DProblem>();

	/** the number of effectively running solvers */
	private final AtomicInteger running = new AtomicInteger(0);

	/**
	 * Constructs an implementation of a decomposed problem solver to retrieve the problem's stats.
	 *
	 * @see kodkod.engine.decomp.DProblemExecutor#DProblemExecutor(Formula, Formula, Bounds, Bounds, Solver, int)
	 */
	public StatsExecutor(Formula f1, Formula f2, Bounds b1, Bounds b2, Solver solver1, Solver solver2, int n) {
		super(new DMonitorImpl(), f1, f2, b1, b2, solver1, solver2, n);
	}

	/**
	 * Registers the solution but never shuts down the executor, since every
	 * integrated problem is expected to terminate.
	 * 
	 * @see kodkod.engine.decomp.DProblemExecutor#end(kkpartition.PProblem)
	 */
	@Override
	public void end(DProblem sol) {
		monitor.newSolution(sol);
		running.decrementAndGet();
	}

	/**
	 * Launches the parallel finders to solve the decomposed problem until the
	 * partial problem is unsatisfiable. The processes are handled by an
	 * executor that launched as many threads as defined by the options.
	 *
	 * @see kodkod.pardinus.DProblemExecutorr#run()
	 */
	@Override
	public void run() {
		Iterator<Solution> configs = solver1.solveAll(formula1, bounds1);
		while (configs.hasNext() && !executor.isShutdown()) {
			while (configs.hasNext() && problem_queue.size() < 200) {
				Solution config = configs.next();
				monitor.newConfig(config);
				if (config.sat()) {
					DProblem problem = new IProblem(config, this);
					problem.setPriority(MIN_PRIORITY);
					problem_queue.add(problem);
				}
			}
			while (!problem_queue.isEmpty() && !executor.isShutdown()) {
				DProblem problem = problem_queue.remove(/* 0 */problem_queue.size() - 1);
				executor.execute(problem);
				running.incrementAndGet();
			}
		}
		executor.shutdown();
		monitor.configsDone();
	}

	/**
	 * Waits until every problem terminates or there is a timeout.
	 * 
	 * @see kodkod.engine.decomp.DProblemExecutor#waitUntil()
	 */
	public Solution waitUntil() throws InterruptedException {
		boolean timeout = executor.awaitTermination(3, TimeUnit.HOURS);
		monitor.done(timeout);
		return null;
	}

}
