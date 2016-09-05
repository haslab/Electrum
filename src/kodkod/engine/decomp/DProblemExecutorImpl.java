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
import java.util.concurrent.BlockingQueue;
import java.util.concurrent.LinkedBlockingQueue;
import java.util.concurrent.RejectedExecutionException;
import java.util.concurrent.atomic.AtomicInteger;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;

/**
 * A concretization of a decomposed problem executor designed to retrieve a
 * single SAT solution. Terminates once a SAT integrated / amalgamated problem
 * is found or when every configuration has been explored.
 * 
 * @see kodkod.engine.decomp.DProblemExecutor
 * @author nmm, ejp
 */
public class DProblemExecutorImpl extends DProblemExecutor {

	/** the queue of solvers to be launched */
	private final List<DProblem> problem_queue = new ArrayList<DProblem>();

	/** the number of effectively running solvers */
	private final AtomicInteger running = new AtomicInteger(0);

	/** the queue of found SAT solutions (or poison) */
	private final BlockingQueue<Solution> solution_queue = new LinkedBlockingQueue<Solution>(10);

	/** whether the amalgamated problem will be launched */
	private final boolean hybrid;

	/** whether the amalgamated solver is currently running */
	private DProblem amalgamated_running;

	/**
	 * Constructs an implementation of a decomposed problem solver with support for hybrid model.
	 *
	 * @see kodkod.engine.decomp.DProblemExecutor#DProblemExecutor(Formula, Formula, Bounds, Bounds, Solver, int)
	 */
	public DProblemExecutorImpl(Formula f1, Formula f2, Bounds b1, Bounds b2, Solver solver1, Solver solver2, int n, boolean it) {
		super(new DMonitorImpl(), f1, f2, b1, b2, solver1, solver2, n);
		this.hybrid = it;
	}

	/**
	 * Registers the solution and shutdowns the executor if the caller is the
	 * amalgamated problem, SAT integrated problem or last integrated problem.
	 * @return 
	 * 
	 * @see kodkod.engine.decomp.DProblemExecutor#end(kkpartition.PProblem)
	 */
	@Override
	public void end(DProblem sol) {
		System.out.println(sol.sat());
		if (Thread.currentThread().isInterrupted()) return;
		try {
			// if the amalgamated terminates...
			if (!(sol instanceof IProblem)) {
				// store the sat or unsat solution
				solution_queue.put(sol.getSolution());
				running.set(1);
				monitor.amalgamatedWon();
				// terminate the integrated problems
				if (!executor.isTerminated())
					executor.shutdownNow();
				// if sat, iterate and launch
				if (sol.sat()) {
					amalgamated_running = sol.next();
					amalgamated_running.start();
				} else
					running.incrementAndGet();
			} 
			// if a integrated terminates...
			else {
				// if it is sat...
				if (sol.sat()) {
					// store the sat solution
					solution_queue.put(sol.getSolution());
					// terminate the amalgamated problem
					if (amalgamated_running != null && amalgamated_running.isAlive()) {
						amalgamated_running.interrupt();
						running.decrementAndGet();
					}
					// iterate and launch
					executor.execute(sol.next());
				} 
				// if it is unsat...
				else {
					running.decrementAndGet();
					// if last running integrated...
					if (monitor.isConfigsDone() && running.get() == 0) {
						// store the unsat solution
						solution_queue.put(sol.getSolution()); 
						// terminate the executor
						if (!executor.isTerminated())
							executor.shutdownNow();
					} 
				}
			}
			monitor.newSolution(sol);
		} catch (InterruptedException e) {
			// was interrupted in the meantime
		} catch (RejectedExecutionException e) {
			// was shutdown in the meantime
		}

	}


	/**
	 * Launches the parallel finders to solve the decomposed problem until the
	 * partial problem is unsatisfiable. The processes are handled by an
	 * executor that launched as many threads as defined by the options.
	 * Launches an amalgamated problem if in hybrid mode.
	 *
	 * @see kodkod.pardinus.DProblemExecutorr#run()
	 */
	@Override
	public void run() {
		// if hybrid mode, launch the amalgamated problem
		if (hybrid) {
			DProblem amalg = new DProblem(this, formula1.and(formula2), merge(bounds1, bounds2));
			amalg.setPriority(MAX_PRIORITY);
			executor.execute(amalg);
			running.incrementAndGet();
			amalgamated_running = amalg;
		}

		Iterator<Solution> configs = solver1.solveAll(formula1, bounds1);
		boolean first = true;

		while (configs.hasNext() && !executor.isShutdown()) {
			// collects a batch of configurations
			while (configs.hasNext() && problem_queue.size() < 200) {
				Solution config = configs.next();

				if (config.unsat()) {
					// when there is no configuration no solver will ever
					// callback so it must be terminated here
					if (first)
						try {
							solution_queue.put(config);
						} catch (InterruptedException e) {
							e.printStackTrace();
						}
				} else {
					monitor.newConfig(config);
					DProblem problem = new IProblem(config, this);
					problem.setPriority(MIN_PRIORITY);
					problem_queue.add(problem);
				}

				first = false;

			}
			// launches a batch of integrated problems
			while (!problem_queue.isEmpty() && !executor.isShutdown()) {
				DProblem problem = problem_queue.remove(0/*problem_queue.size()-1*/);
				try {
					executor.execute(problem);
				} catch (RejectedExecutionException e) {
					// if it was shutdown in the meantime
				}
				running.incrementAndGet();
			}
		}
//		executor.shutdown();
		monitor.configsDone();
	}

	/**
	 * Waits until a single solutions is added to the solution queue.
	 * 
	 * @see kodkod.engine.decomp.DProblemExecutor#waitUntil()
	 */
	@Override
	public Solution waitUntil() throws InterruptedException {
		Solution sol = solution_queue.take();
		monitor.done(false);
		return sol;
	}

	/**
	 * Merges two problem bounds into a single one.
	 * 
	 * @param b1
	 *            the base bounds.
	 * @param b2
	 *            the bounds to be merged.
	 * @return the merged bounds.
	 */
	private static Bounds merge(Bounds b1, Bounds b2) {
		Bounds b3 = b1.clone();
		for (Relation r : b2.relations()) {
			b3.bound(r, b2.lowerBound(r), b2.upperBound(r));
		}
		return b3;
	}

}
