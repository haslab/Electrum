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

import java.util.HashSet;

import kodkod.ast.BinaryTempFormula;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.TempExpression;
import kodkod.ast.UnaryTempFormula;
import kodkod.ast.VarRelation;
import kodkod.ast.visitor.AbstractDetector;
import kodkod.engine.config.TemporalOptions;
import kodkod.instance.Bounds;

/**
 * Translates temporal {@link Formula formulas} and {@link Bounds bounds}, with
 * respect to given {@link TemporalOptions temporal options}.
 *
 * @author Eduardo Pessoa, nmm (pt.uminho.haslab)
 */
public class TemporalTranslator {

    /** Relations representing the trace constants. **/
    public static Relation TIME = Relation.unary("Time");
    public static Relation INIT = Relation.unary("init");
    public static Relation END = Relation.unary("end");
    public static Relation NEXT = Relation.binary("next");
    public static Relation TRACE = Relation.binary("trace");
    public static Relation LOOP = Relation.binary("loop");

    /** The name assigned to {@link #TIME time} atoms. */
    public static String TIMEATOM = "Time";

    /**
     * Translates {@link VarRelation variable relation} bounds into its standard
     * representation, by appending the {@link #TIME time sig} to the bound. The
     * bounds of static relations should remain unchanged. The temporal options
     * will define the maximum size of the trace. The returned temporal bounds
     * also store the mapping of the variable relations into their expanded
     * static version.
     * 
     * @param bounds
     *            the bounds to be expanded.
     * @param options
     *            the temporal options.
     * @return the expanded variable bounds and the mapping between the old and
     *         new sigs.
     */
    public static ExpandedTemporalBounds translate(Bounds bounds,
	    TemporalOptions<?> options) {
	ExpandedTemporalBounds tbounds = new ExpandedTemporalBounds(bounds,
		options.maxTraceLength());
	return tbounds;
    }

    /**
     * Converts an LTL temporal formula into its FOL static representation,
     * provided the previous expansion of the bounds and temporal options. The
     * formula is previously converted into negative normal form to guarantee
     * the correct translation of the temporal operators.
     * 
     * @param formula
     *            the temporal formula to be expanded.
     * @param bounds
     *            the expanded bounds.
     * @param options
     *            the temporal options.
     * @return the static version of the temporal formula.
     */
    public static Formula translate(Formula formula, ExpandedTemporalBounds bounds,
	    TemporalOptions<?> options) {
	if (isTemporal(bounds))
	    throw new UnsupportedOperationException(
		    "Variable bounds must be previously expanded: " + bounds);
	NNFReplacer nnf = new NNFReplacer();
	Formula nnfFormula = formula.accept(nnf);

	LTL2FOLTranslator addTimeToFormula = new LTL2FOLTranslator(
		bounds.getExtendedVarRelations());
	Formula result = addTimeToFormula.translate(nnfFormula);

	return result;
    }

    /**
     * Checks whether an AST node has temporal constructs.
     * 
     * @param node
     *            the node to be checked.
     * @return whether the node has temporal constructs.
     */
    public static boolean isTemporal(Node node) {
	AbstractDetector det = new AbstractDetector(new HashSet<Node>()) {
	    @Override
	    public Boolean visit(UnaryTempFormula tempFormula) {
		return cache(tempFormula, true);
	    }

	    @Override
	    public Boolean visit(BinaryTempFormula tempFormula) {
		return cache(tempFormula, true);
	    }

	    @Override
	    public Boolean visit(TempExpression tempExpr) {
		return cache(tempExpr, true);
	    }

	    @Override
	    public Boolean visit(Relation relation) {
		return cache(relation, relation instanceof VarRelation);
	    }
	};
	return (boolean) node.accept(det);
    }

    /**
     * Checks whether a set of bounds binds variable relations.
     * 
     * @param bounds
     *            the bounds to be checked.
     * @return whether the bounds bind variable relations.
     */
    public static boolean isTemporal(Bounds bounds) {
	for (Relation r : bounds.relations())
	    if (r instanceof VarRelation)
		return true;
	return false;
    }
}
