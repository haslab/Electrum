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

import java.util.Iterator;

import kodkod.ast.Formula;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.instance.Bounds;

/**
 * A decomposed model finding problem.
 * @author nmm
 *
 */
public class DProblem extends Thread {

	final private Solver solver;
	
	private Iterator<Solution> solutions;
	private Solution solution;
	final public Bounds bounds;
	final public Formula formula;
	final public DProblemExecutor executor;

	public DProblem(DProblemExecutor executor, Formula formula, Bounds bnds) {
		this.executor = executor;
		if (this.executor != null) {
			solver = executor.solver2;
			this.bounds = bnds;
			this.formula = formula;
		} else {
			this.solver = null;
			this.formula = null;
			this.bounds = null;
		}
	}

	protected DProblem(DProblemExecutor manager, Formula formula, Bounds bnds, Iterator<Solution> sols) {
		this.executor = manager;
		this.solver = manager.solver2;
		this.bounds = bnds;
		this.formula = formula;
		this.solutions = sols;
	}
	
	public void run() {
		if (solutions == null) {
			solutions = solver.solveAll(formula,bounds);
			solver.free();
		}
		solution = solutions.next();
		executor.end(this);
	}

	public boolean sat() {
		return solution.sat();
	}
	
	public DProblem next() {
		return new DProblem(executor, formula, bounds, solutions);
	}

	public Solution getSolution() {
		if (solution == null && solutions.hasNext()) solution = solutions.next();
		return solution;
	}
	
	protected Iterator<Solution> getIterator() {
		return solutions;
	}
	
}