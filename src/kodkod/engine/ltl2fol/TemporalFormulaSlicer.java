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

import kodkod.ast.*;
import kodkod.ast.visitor.AbstractReplacer;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.instance.Bounds;
import static kodkod.ast.operator.FormulaOperator.AND;

import java.util.*;

/**
 * Slices a temporal {@link Formula formula} into a static and a dynamic
 * component, the former containing constraints without temporal operators and
 * without references to variable relations. The formula should be provided in
 * negative normal form in order to optimize the slicing.
 * 
 * @author Eduardo Pessoa
 * @modified nmm (pt.uminho.haslab)
 */
// TODO: use Kodkod's FormulaFlattener to retrieve the top-level conjuncts
public class TemporalFormulaSlicer extends AbstractReplacer implements
		ReturnVisitor<Expression, Formula, Decls, IntExpression> {

	private enum Context {
		formulaAnalysis, formulaExpansion
	};

	private boolean varRelation = false;
	private List<Formula> dynamicFormulas;
	private List<Formula> staticFormulas;
	private Bounds dynamicBounds;
	private Bounds staticBounds;
	private Context context;

	public TemporalFormulaSlicer(Formula formula, Bounds bounds) {
		super(new HashSet<Node>());
		this.dynamicFormulas = new ArrayList<Formula>();
		this.staticFormulas = new ArrayList<Formula>();
		this.context = Context.formulaExpansion;
		formula.accept(this);
		splitBounds(bounds);
	}

	private void splitBounds(Bounds bounds) {
		// TODO: targets will be lost
		staticBounds = new Bounds(bounds.universe());
		dynamicBounds = new Bounds(bounds.universe());
		for (Relation r : bounds.relations()) {
			if (r instanceof VarRelation)
				dynamicBounds.bound(r, bounds.lowerBound(r), bounds.upperBound(r));
			else
				staticBounds.bound(r, bounds.lowerBound(r), bounds.upperBound(r));
		}
	}

	public List<Formula> getDynamicFormulas() {
		return dynamicFormulas;
	}

	public List<Formula> getStaticFormulas() {
		return staticFormulas;
	}
	
	public Bounds getDynamicBounds() {
		return dynamicBounds;
	}

	public Bounds getStaticBounds() {
		return staticBounds;
	}


	@Override
	public Expression visit(Relation relation) {
		if (relation instanceof VarRelation) {
			this.varRelation = true;
		}
		return relation;
	}

	@Override
	public Formula visit(NaryFormula naryFormula) {
		Formula[] arrayOfFormula = new Formula[naryFormula.size()];
		for (int j = 0; j < arrayOfFormula.length; j++) {
			Formula localFormula2 = naryFormula.child(j);
			if (context == Context.formulaExpansion) {
				if (((localFormula2 instanceof BinaryFormula) && ((BinaryFormula) localFormula2).op() == AND)
						|| (localFormula2 instanceof NaryFormula && ((NaryFormula) localFormula2).op() == AND)) {
					arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
				} else {
					context = Context.formulaAnalysis;
					arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
					context = Context.formulaExpansion;
					if (varRelation) {
						this.varRelation = false;
						this.dynamicFormulas.add(arrayOfFormula[j]);
					} else {
						this.staticFormulas.add(arrayOfFormula[j]);
					}
				}
			} else {
				arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
			}
		}
		return Formula.compose(naryFormula.op(), arrayOfFormula);

	}

	@Override
	public Formula visit(BinaryFormula binaryFormula) {
		Formula left;
		Formula right;
		if (context == Context.formulaExpansion && binaryFormula.op() == AND) {
			if ((binaryFormula.left() instanceof BinaryFormula && ((BinaryFormula) binaryFormula.left()).op() == AND)
					|| (binaryFormula.left() instanceof NaryFormula && ((NaryFormula) binaryFormula.left()).op() == AND)) {
				left = binaryFormula.left().accept(this);
			} else {
				context = Context.formulaAnalysis;
				left = binaryFormula.left().accept(this);
				context = Context.formulaExpansion;
				if (varRelation) {
					this.varRelation = false;
					this.dynamicFormulas.add(left);
				} else {
					this.staticFormulas.add(left);
				}
			}

			if ((binaryFormula.right() instanceof BinaryFormula && ((BinaryFormula) binaryFormula.right()).op() == AND)
					|| (binaryFormula.right() instanceof NaryFormula && ((NaryFormula) binaryFormula.right()).op() == AND)) {
				right = binaryFormula.right().accept(this);
			} else {
				context = Context.formulaAnalysis;
				right = binaryFormula.right().accept(this);
				context = Context.formulaExpansion;
				if (varRelation) {
					this.varRelation = false;
					this.dynamicFormulas.add(right);
				} else {
					this.staticFormulas.add(right);
				}
			}

		} else {
			left = binaryFormula.left().accept(this);
			right = binaryFormula.right().accept(this);
		}
		return left.compose(binaryFormula.op(), right);

	}

}
