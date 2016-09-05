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

import kodkod.ast.Relation;
import kodkod.engine.Solution;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.TupleSet;

public class IProblem extends DProblem {

	final public Solution config;

	public IProblem(Solution cfg, DProblemExecutor manager) {
		super(manager, manager.formula2, configBounds(manager, cfg));
		this.config = cfg;
	}
	
	public IProblem(Solution cfg, DProblemExecutor manager, Iterator<Solution> sols) {
		super(manager, manager.formula2, configBounds(manager, cfg), sols);
		this.config = cfg;
	}
	
	/**
	 * Sets a configuration solution as exact bounds for the problem.
	 * @param b1
	 * @param b2
	 * @param s
	 * @return
	 */
	private static Bounds configBounds(DProblemExecutor manager, Solution s) {
		
		Bounds b3 = manager.bounds2.clone();

		for (Relation e : manager.bounds1.upperBounds().keySet()) {
			if (getTupleConfiguration(e.name(), s.instance()) != null) {
				b3.boundExactly(e, getTupleConfiguration(e.name(), s.instance()));
			}
		}

		for (Integer i : s.instance().ints().toArray())
			b3.boundExactly(i, b3.universe().factory().setOf(i));

		return b3;
	}

	private static TupleSet getTupleConfiguration(String name, Instance s) {
		for (Relation r : s.relationTuples().keySet()) {
			if (r.name().equals(name)) {
				return s.relationTuples().get(r);
			}
		}
		return null;
	}

	public IProblem next() {
		return new IProblem(config, executor, getIterator());
	}
	
}