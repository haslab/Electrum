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

import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;
import java.util.concurrent.TimeUnit;

import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;


/**
 * An executor that effectively handles a decomposed model finding problem problem,
 * defined by a pair of bounds, a pair of formulas and the solver that will be launched
 * in parallel. It is also defined by the number of threads that will be launched.
 * 
 * @author nmm, ejp
 *
 */
abstract public class DProblemExecutor extends Thread {

	/** the decomposed problem bounds */
	protected final Bounds bounds1, bounds2;
	
	/** the decomposed problem formulas */
	protected final Formula formula1, formula2;

	/** the underlying regular solver */
	protected final Solver solver1, solver2;

	/** the executor managing the launching of the threads 
	 * TODO: replace by new ThreadPoolExecutor(corePoolSize, maximumPoolSize, keepAliveTime, unit, workQueue) to manage LIFO
	 */
	public final ExecutorService executor;

	/** a reporter that monitors the solving process */
	public final DMonitor monitor;

	/**
	 * Constructs an effective decomposed problem executor for a decomposed model finding problem
	 * and the number of desired parallel solvers.
	 * 
	 * @param f1 the partial problem formula.
	 * @param f2 the remainder problem formula.
	 * @param b1 the partial problem bounds.
	 * @param b2 the remainder problem bounds.
	 * @param solver the solver that will solve the integrated problems.
	 * @param n the number of parallel solver threads.
	 */
	public DProblemExecutor(DMonitor rep, Formula f1, Formula f2, Bounds b1, Bounds b2, Solver solver1, Solver solver2, int n) {
		this.formula1 = f1;
		this.formula2 = f2;
		this.bounds1 = b1; 
		this.bounds2 = b2; 
		this.solver1 = solver1;
		this.solver2 = solver2;
		this.executor = Executors.newFixedThreadPool(n);
		this.monitor = rep;
	}
	
	/**
	 * Called by one of the parallel integrated model finders when finished solving.
	 * 
	 * @param sol the solution calculated by the caller.
	 */
	public abstract void end(DProblem sol);

	/**
	 * Starts the solving process.
	 */
	public abstract void run();

	/**
	 * Waits until the executor terminates.
	 * @return
	 * @throws InterruptedException if interrupted while waiting.
	 */
	public abstract Solution waitUntil() throws InterruptedException;

	/**
	 * Terminates the thread executor and the running solvers.
	 * 
	 * @throws InterruptedException if interrupted while waiting.
	 */
	public void terminate() throws InterruptedException {
		if (!executor.isShutdown())
			executor.shutdownNow();
		if (!executor.isTerminated()) {
			boolean timeout = executor.awaitTermination(1, TimeUnit.HOURS);
			monitor.terminated(timeout);
		}
	}
}