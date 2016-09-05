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
package kodkod.engine.ltl2fol;

import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.instance.*;

import java.util.*;

/**
 * An extension to the regular Kodkod {@link Bounds bounds} that stores
 * information regarding its origin from bounds over {@link VarRelation variable
 * relations}. Translates {@link VarRelation variable relation} bounds into its
 * standard representation, by appending the {@link TemporalTranslator#TIME time
 * sig} to the bound. The bounds of static relations should remain unchanged.
 * The temporal options will define the maximum size of the trace. It will also
 * store the mapping of the variable relations into their expanded versions
 *
 * @author Eduardo Pessoa, nmm (pt.uminho.haslab)
 */
public class ExpandedTemporalBounds extends Bounds {

	/**
	 * The number of distinguished states in the trace.
	 */
	private int numberOfTimes;

	/**
	 * The originally static relations.
	 */
	private Set<Relation> staticRelations;

	/**
	 * A mapping that identifies the variable relations that were extended into
	 * static relations.
	 */
	private Map<String, Relation> extendedVarRelations;

	public ExpandedTemporalBounds(Bounds oldBounds, int numberOfTimes) {
		super(createUniverse(oldBounds, numberOfTimes));
		this.staticRelations = new HashSet<Relation>();
		this.numberOfTimes = numberOfTimes;
		this.extendedVarRelations = new HashMap<String, Relation>();
		this.expand(oldBounds);
	}

	/**
	 * The set of static relations that were extended from variable relations,
	 * plus the constant relations representing the trace.
	 * 
	 * @return the extended and trace relations.
	 */
	public Set<Relation> getDynamicRelations() {
		Set<Relation> dynamicRelations = new HashSet<Relation>(extendedVarRelations.values());

		dynamicRelations.add(TemporalTranslator.TIME);
		dynamicRelations.add(TemporalTranslator.INIT);
		dynamicRelations.add(TemporalTranslator.END);
		dynamicRelations.add(TemporalTranslator.NEXT);
		dynamicRelations.add(TemporalTranslator.LOOP);
		dynamicRelations.add(TemporalTranslator.TRACE);

		return dynamicRelations;
	}

	/**
	 * The static relations resulting from the extension of the variable
	 * relations.
	 * 
	 * @return a mapping from the relations names into their expanded version.
	 */
	public Map<String, Relation> getExtendedVarRelations() {
		return extendedVarRelations;
	}

	/**
	 * The set of static relations that were already static.
	 * 
	 * @return the originally static relations.
	 */
	public Set<Relation> getStaticRelations() {
		return staticRelations;
	}

	/**
	 * Expands the old bounds by converting the bounds over variable relations
	 * into regular bounds with {@link TemporalTranslator#TIME temporal} atoms
	 * appended. It also bounds the constant variables representing the trace.
	 * 
	 * @param oldBounds
	 *            the bounds with variable relations to be expanded.
	 */
	private void expand(Bounds oldBounds) {
		TupleSet tupleSetTime = universe().factory().range(
				universe().factory().tuple(new Object[] { TemporalTranslator.TIMEATOM + "0" }),
				universe().factory().tuple(new Object[] { TemporalTranslator.TIMEATOM + (this.numberOfTimes - 1) }));
		for (Relation r : oldBounds.relations()) {
			if (r instanceof VarRelation) {
				this.makeNewTuplesFromOldBounds(oldBounds, (VarRelation) r, tupleSetTime);
			} else {
				this.makeNewTuplesFromOldBounds(oldBounds, r);
			}
		}

		super.bound(TemporalTranslator.TIME, tupleSetTime);
		super.bound(TemporalTranslator.INIT, tupleSetTime);
		super.bound(TemporalTranslator.END, tupleSetTime);
		super.bound(TemporalTranslator.NEXT, tupleSetTime.product(tupleSetTime));
		super.bound(TemporalTranslator.LOOP, tupleSetTime.product(tupleSetTime));
		super.bound(TemporalTranslator.TRACE, tupleSetTime.product(tupleSetTime));
	}

	/**
	 * Create a new universe by duplicating the original one and creating a
	 * given number of {@link TemporalTranlator#TIME time} atoms.
	 *
	 * @param oldBounds
	 *            the original bounds.
	 * @param numberOfTimes
	 *            the number of time atoms.
	 * @return a new universe with the atoms of the original one plus the time
	 *         ones.
	 */
	private static Universe createUniverse(Bounds oldBounds, int numberOfTimes) {
		List<Object> newAtoms = new ArrayList<Object>();
		Iterator<Object> it = oldBounds.universe().iterator();
		while (it.hasNext()) {
			newAtoms.add(it.next());
		}

		for (int i = 0; i < numberOfTimes; i++) {
			newAtoms.add(TemporalTranslator.TIMEATOM + i);
		}

		return new Universe(newAtoms);
	}

	/**
	 * Converts the existing bounds of a variable relation into ones with the
	 * current universe, appending the {@link TemporalTranlator#TIME time}
	 * atoms.
	 * 
	 * @param oldBounds
	 *            the original bounds.
	 * @param relation
	 *            the variable relation whose bounds are to be expanded.
	 * @param timeAtoms
	 *            the time atoms in the universe.
	 */
	private void makeNewTuplesFromOldBounds(Bounds oldBounds, VarRelation relation, TupleSet timeAtoms) {
		TupleSet tupleSetL = convert(oldBounds.lowerBounds().get(relation));
		TupleSet tupleSetU = convert(oldBounds.upperBounds().get(relation));

		super.bound(getExpandedRelation(relation), tupleSetL.product(timeAtoms), tupleSetU.product(timeAtoms));
	}

	/**
	 * Converts the existing bounds of a static relation into ones with the
	 * current universe.
	 * 
	 * @param oldBounds
	 *            the original bounds.
	 * @param relation
	 *            the variable relation whose bounds are to be expanded.
	 */
	private void makeNewTuplesFromOldBounds(Bounds oldBounds, Relation relation) {
		TupleSet tupleSetL = convert(oldBounds.lowerBounds().get(relation));
		TupleSet tupleSetU = convert(oldBounds.upperBounds().get(relation));

		staticRelations.add(relation);
		super.bound(relation, tupleSetL, tupleSetU);
	}

	/**
	 * Converts an existing tuple set into an identical tuple set with the
	 * current universe.
	 * 
	 * @param ts
	 *            the existing tuple set
	 * @return the converted tuple set
	 */
	private TupleSet convert(TupleSet ts) {
		TupleSet tupleSet = universe().factory().noneOf(ts.arity());
		Iterator<Tuple> itr = ts.iterator();
		while (itr.hasNext()) {
			Tuple t = itr.next();
			List<Object> l = new ArrayList<Object>();
			for (int i = 0; i < t.arity(); i++) {
				l.add(t.atom(i));
			}
			tupleSet.add(universe().factory().tuple(l));
		}
		return tupleSet;
	}

	/**
	 * Returns the a static relation corresponding to the extension of a
	 * variable relation, by increasing its arity by 1. Creates it if being
	 * called for the first time.
	 * 
	 * @param v
	 *            the variable relation to be expanded.
	 * @return the expanded version.
	 */
	private Relation getExpandedRelation(VarRelation v) {
		Relation e = extendedVarRelations.get(v.name());
		if (e == null) {
			Relation varRelation = Relation.nary(v.name(), v.arity() + 1);
			extendedVarRelations.put(v.name(), varRelation);
			return varRelation;
		} else {
			return e;
		}
	}

}
