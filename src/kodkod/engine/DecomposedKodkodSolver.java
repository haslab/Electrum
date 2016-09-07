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
package kodkod.engine;

import java.util.Iterator;
import java.util.NoSuchElementException;

import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.config.DecomposedOptions.DMode;
import kodkod.engine.decomp.DProblemExecutor;
import kodkod.engine.decomp.DProblemExecutorImpl;
import kodkod.engine.decomp.StatsExecutor;
import kodkod.instance.Bounds;

/**
 * A computational engine for solving relational satisfiability problems. Such a
 * problem is described by a pair {@link kodkod.ast.Formula formulas} in first
 * order relational logic; a pair of finite {@link kodkod.instance.Bounds
 * bounds} on the value of each {@link Relation relation} constrained by the
 * respective formulas; and a set of {@link kodkod.pardinus.decomp.DOptions options}
 * built over regular Kodkod {@link kodkod.engine.config.Options options}. The
 * decomposed solve relies on regular Kodkod {@link kodkod.engine.Solver
 * solvers} that are deployed in parallel. The solver returns a
 * {@link kodkod.engine.decomp.DProblem decomposed solution} that can be iterated.
 * 
 * @author nmm, ejp
 *
 */
public class DecomposedKodkodSolver implements DecomposedSolver<ExtendedOptions>, BoundedSolver<ExtendedOptions> {

	/** the regular Kodkod solver used in the parallelization */
	final private Solver solver1, solver2;

	/** a manager for the decomposed solving process */
	private DProblemExecutor executor;

	/** the decomposed problem options */
	final private ExtendedOptions options;

	/**
	 * Constructs a new decomposed solver built over a standard Kodkod
	 * {@link kodkod.engine.Solver solver}. The solving
	 * {@link kodkod.engine.config.Options options} are retrieved from the
	 * regular solver.
	 * 
	 * @param solver
	 *            the regular solver over which the decomposed solver is built.
	 * @throws IllegalArgumentException
	 *             if the solver is not incremental.
	 */
	public DecomposedKodkodSolver() {
		this.options = new ExtendedOptions();
		this.solver1 = new Solver((Options) options.configOptions());
		this.solver2 = new Solver(options);
	}
	
	public DecomposedKodkodSolver(ExtendedOptions options) {
		this.options = options;
		this.solver1 = new Solver((Options) options.configOptions());
		this.solver2 = new Solver(options);
	}

	/**
	 * Solves a decomposed model finding problem, comprised by a pair of
	 * {@link kodkod.ast.Formula formulas} and a pair of
	 * {@link kodkod.instance.Bounds bounds}. Essentially launches an
	 * {@link kodkod.engine.decomp.DProblemExecutor executor} to handle the
	 * decomposed problem in parallel, given the defined
	 * {@link kodkod.pardinus.decomp.DOptions options}.
	 * @param f1
	 *            the partial problem formula.
	 * @param f2
	 *            the remainder problem formula.
	 * @param b1
	 *            the partial problem bounds.
	 * @param b2
	 *            the remainder problem bounds.
	 * 
	 * @requires f1 to be defined over b1 and f2 over b2.
	 * @return a decomposed solution.
	 * @throws InterruptedException
	 *             if the solving process is interrupted.
	 */
	@Override
	public Solution solve(Formula f1, Formula f2, Bounds b1, Bounds b2) throws InterruptedException {
		if (!options.configOptions().solver().incremental())
			throw new IllegalArgumentException("An incremental solver is required to iterate the configurations.");
		if (options.decomposedMode() == DMode.EXHAUSTIVE)
			executor = new StatsExecutor(f1, f2, b1, b2, solver1, solver2, options.threads());
		else if (options.decomposedMode() == DMode.HYBRID)
			executor = new DProblemExecutorImpl(f1, f2, b1, b2, solver1, solver2, options.threads(), true);
		else
			executor = new DProblemExecutorImpl(f1, f2, b1, b2, solver1, solver2, options.threads(), false);
		executor.start();
		Solution sol = executor.waitUntil();
		executor.terminate();
		return sol;
	}

	/**
	 * Retrieves the decomposed problem executor that handled the decomposed problem.
	 * 
	 * @return the decomposed problem executor that solved the problem.
	 */
	public DProblemExecutor executor() {
		return executor;
	}

	/**
	 * Releases the resources, if any.
	 */
	public void free() {}

	@Override
	public Solution solve(Formula formula, Bounds bounds) {
		Solution s = null;
		try {
			s = solve(formula, Formula.TRUE, bounds, new Bounds(bounds.universe()));
		} catch (InterruptedException e) {
			// Should throw AbortedException
			e.printStackTrace();
		}
		return s;
	}

	@Override
	public ExtendedOptions options() {
		return options;
	}

	@Override
	public Iterator<Solution> solveAll(Formula formula1, Formula formula2, Bounds bounds1, Bounds bounds2) {
		// nmm: this was commented, why?
		if (!options.solver().incremental())
			throw new IllegalArgumentException("cannot enumerate solutions without an incremental solver.");
		
		return new DSolutionIterator(formula1, formula2, bounds1, bounds2, options, solver1, solver2); 
	}
	
	private static class DSolutionIterator implements Iterator<Solution> {
		private DProblemExecutor executor;

		/**
		 * Constructs a solution iterator for the given formula, bounds, and options.
		 */
		DSolutionIterator(Formula formula1, Formula formula2, Bounds bounds1, Bounds bounds2, ExtendedOptions options, Solver solver1, Solver solver2) {
			if (options.decomposedMode() == DMode.EXHAUSTIVE)
				executor = new StatsExecutor(formula1, formula2, bounds1, bounds2, solver1, solver2, options.threads());
			else if (options.decomposedMode() == DMode.HYBRID)
				executor = new DProblemExecutorImpl(formula1, formula2, bounds1, bounds2, solver1, solver2, options.threads(), true);
			else
				executor = new DProblemExecutorImpl(formula1, formula2, bounds1, bounds2, solver1, solver2, options.threads(), false);
			executor.start();
		}
		
		/**
		 * Returns true if there is another solution.
		 * @see java.util.Iterator#hasNext()
		 */
		public boolean hasNext() {  return !executor.executor.isTerminated(); }
		
		/**
		 * Returns the next solution if any.
		 * @see java.util.Iterator#next()
		 */
		public Solution next() {
			if (!hasNext()) throw new NoSuchElementException();			
			try {
				return executor.waitUntil();
			} catch (InterruptedException e) {
				try {
					executor.terminate();
				} catch (InterruptedException e1) {
					// TODO Auto-generated catch block
					e1.printStackTrace();
				}
				// Should throw AbortedException
				e.printStackTrace();
			}
			return null;
		}

		/** @throws UnsupportedOperationException */
		public void remove() { throw new UnsupportedOperationException(); }
		
	}
	

}
