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
package kodkod.instance;

import java.util.HashMap;
import java.util.Map;

import kodkod.ast.Relation;

/**
 * Represents a temporal model (an instance) of a temporal relational formula,
 * which is a mapping from time instants to a mapping from
 * {@link kodkod.ast.Relation relations} and integers to
 * {@link kodkod.instance.TupleSet sets of tuples} drawn from a given
 * {@link kodkod.instance.Universe universe}. The methods inherited from regular
 * {@link kodkod.instance.Instance instances} act upon the initial state.
 * 
 * @author nmm
 *
 */
public class TemporalInstance extends Instance {
	private final Map<String,Relation> expandedRelations;
	
	public TemporalInstance(Universe universe) {
		super(universe);
		if (universe == null)
			throw new NullPointerException("universe=null");
		this.expandedRelations = new HashMap<String, Relation>();
	}

	public TemporalInstance(Universe universe, Map<String, Relation> extendedVarRelations) {
		super(universe);
		if (universe == null)
			throw new NullPointerException("universe=null");
		this.expandedRelations = extendedVarRelations;
	}

	/**
	 * Maps relation names to their expanded representation.
	 * @return
	 */
	public Map<String, Relation> getMaps() {
		return expandedRelations;
	}

}
