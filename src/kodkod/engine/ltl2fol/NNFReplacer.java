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

import static kodkod.ast.operator.FormulaOperator.AND;
import static kodkod.ast.operator.FormulaOperator.OR;

import java.util.HashSet;

import kodkod.ast.BinaryFormula;
import kodkod.ast.BinaryTempFormula;
import kodkod.ast.ComparisonFormula;
import kodkod.ast.ConstantFormula;
import kodkod.ast.Formula;
import kodkod.ast.IntComparisonFormula;
import kodkod.ast.MultiplicityFormula;
import kodkod.ast.NaryFormula;
import kodkod.ast.Node;
import kodkod.ast.NotFormula;
import kodkod.ast.QuantifiedFormula;
import kodkod.ast.RelationPredicate;
import kodkod.ast.UnaryTempFormula;
import kodkod.ast.visitor.AbstractReplacer;

/**
 * Converts an LTL temporal formula into its negated normal form (NNF), by
 * propagating negations down LTL and FOL quantifiers.
 * 
 * @author Eduardo Pessoa, nmm (pt.uminho.haslab)
 */
//TODO: build on top of Kodkod's FormulaFlattener?
public class NNFReplacer extends AbstractReplacer {

	/** Whether the current node is in a negated context. */
	private boolean negated = false;

	public NNFReplacer() {
		super(new HashSet<Node>());
	}

	@Override
	public Formula visit(IntComparisonFormula intComparisonFormula) {
		if (negated)
			return intComparisonFormula.not();
		else
			return intComparisonFormula;
	}

	@Override
	public Formula visit(QuantifiedFormula quantifiedFormula) {
		if (negated) {
			switch (quantifiedFormula.quantifier()) {
			case ALL:
				return quantifiedFormula.formula().accept(this).forSome(quantifiedFormula.decls());
			case SOME:
				return quantifiedFormula.formula().accept(this).forAll(quantifiedFormula.decls());
			default:
				negated = !negated;
				Formula temp = quantifiedFormula.accept(this);
				negated = !negated;
				return temp.not();
			}
		} else {
			Formula f = quantifiedFormula.formula().accept(this);
			return (QuantifiedFormula) f.quantify(quantifiedFormula.quantifier(), quantifiedFormula.decls());
		}
	}

	@Override
	public Formula visit(NaryFormula naryFormula) {
		Formula[] arrayOfFormula = new Formula[naryFormula.size()];
		if (negated) {
			switch (naryFormula.op()) {
			case AND:
				for (int j = 0; j < arrayOfFormula.length; j++) {
					Formula localFormula2 = naryFormula.child(j);
					arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
				}
				return Formula.compose(OR, arrayOfFormula);
			case OR:
				for (int j = 0; j < arrayOfFormula.length; j++) {
					Formula localFormula2 = naryFormula.child(j);
					arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
				}
				return Formula.compose(AND, arrayOfFormula);
			default:
				negated = !negated;
				for (int j = 0; j < arrayOfFormula.length; j++) {
					Formula localFormula2 = naryFormula.child(j);
					arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
				}
				negated = !negated;
				return Formula.compose(naryFormula.op(), arrayOfFormula).not();
			}
		} else {
			for (int j = 0; j < arrayOfFormula.length; j++) {
				Formula localFormula2 = naryFormula.child(j);
				arrayOfFormula[j] = ((Formula) localFormula2.accept(this));
			}
			return Formula.compose(naryFormula.op(), arrayOfFormula);
		}

	}

	@Override
	public Formula visit(BinaryFormula binaryFormula) {
		Formula left_t, right_t, left_f, right_f;
		if (negated) {
			switch (binaryFormula.op()) {
			case IMPLIES: // !(a => b) = !(!a || b) = a && !b
				right_f = binaryFormula.right().accept(this);
				negated = !negated;
				left_t = binaryFormula.left().accept(this);
				negated = !negated;
				return left_t.and(right_f);
			case IFF: // !(a <=> b) = !( (a | !b) & (!a | b)) = !(a | !b) | !(!
						// a | b) = (!a & b) | (a & !b)
				negated = !negated;
				left_t = binaryFormula.left().accept(this);
				right_t = binaryFormula.right().accept(this);
				negated = !negated;
				left_f = binaryFormula.left().accept(this);
				right_f = binaryFormula.right().accept(this);
				return (left_f.and(right_t)).or(left_t.and(right_f));
			case AND:
				left_f = binaryFormula.left().accept(this);
				right_f = binaryFormula.right().accept(this);
				return left_f.or(right_f);
			case OR:
				left_f = binaryFormula.left().accept(this);
				right_f = binaryFormula.right().accept(this);
				return left_f.and(right_f);
			default:
				negated = !negated;
				left_t = binaryFormula.left().accept(this);
				right_t = binaryFormula.right().accept(this);
				negated = !negated;
				return left_t.compose(binaryFormula.op(), right_t).not();
			}
		} else {
			switch (binaryFormula.op()) {
			case IMPLIES: // (a => b) = (!a || b)
				right_t = binaryFormula.right().accept(this);
				negated = !negated;
				left_f = binaryFormula.left().accept(this);
				negated = !negated;
				return left_f.or(right_t);
			case IFF: // (a <=> b) = ((a | !b) & (!a | b))
				left_t = binaryFormula.left().accept(this);
				right_t = binaryFormula.right().accept(this);
				negated = !negated;
				left_f = binaryFormula.left().accept(this);
				right_f = binaryFormula.right().accept(this);
				negated = !negated;
				return (left_t.or(right_f)).and(left_f.or(right_t));
			default:
				left_t = binaryFormula.left().accept(this);
				right_t = binaryFormula.right().accept(this);
				return left_t.compose(binaryFormula.op(), right_t);
			}
		}

	}

	@Override
	public Formula visit(NotFormula notFormula) {
		negated = !negated;
		Formula temp = notFormula.formula().accept(this);
		negated = !negated;
		return temp;
	}

	@Override
	public Formula visit(ConstantFormula constantFormula) {
		if (negated)
			return constantFormula.not();
		else
			return constantFormula;
	}

	@Override
	public Formula visit(ComparisonFormula comparisonFormula) {
		if (negated)
			return comparisonFormula.not();
		else
			return comparisonFormula;
	}

	@Override
	public Formula visit(MultiplicityFormula multiplicityFormula) {
		if (negated)
			return multiplicityFormula.not();
		else
			return multiplicityFormula;
	}

	@Override
	public Formula visit(RelationPredicate relationPredicate) {
		if (negated)
			return relationPredicate.not();
		else
			return relationPredicate;
	}

	@Override
	public Formula visit(UnaryTempFormula unaryTempFormula) {
		if (negated) {
			switch (unaryTempFormula.op()) {
			case ALWAYS:
				return unaryTempFormula.formula().accept(this).eventually();
			case EVENTUALLY:
				return unaryTempFormula.formula().accept(this).always();
			case HISTORICALLY:
				return unaryTempFormula.formula().accept(this).once();
			case ONCE:
				return unaryTempFormula.formula().accept(this).historically();
			case NEXT:
				return unaryTempFormula.formula().accept(this).next();
			case PREVIOUS:
				return unaryTempFormula.formula().accept(this).previous();
			default:
				negated = !negated;
				Formula temp = unaryTempFormula.formula().accept(this);
				negated = !negated;
				return temp.compose(unaryTempFormula.op()).not();
			}
		} else {
			Formula f = unaryTempFormula.formula().accept(this);
			return f.compose(unaryTempFormula.op());
		}
	}

	@Override
	public Formula visit(BinaryTempFormula binaryTempFormula) {
		if (negated) {
			switch (binaryTempFormula.op()) {
			case UNTIL:
				return binaryTempFormula.left().accept(this).release(binaryTempFormula.right().accept(this));
			case RELEASE:
				return binaryTempFormula.left().accept(this).until(binaryTempFormula.right().accept(this));
			default:
				negated = !negated;
				Formula temp1 = binaryTempFormula.left().accept(this);
				Formula temp2 = binaryTempFormula.right().accept(this);
				negated = !negated;
				return temp1.compose(binaryTempFormula.op(), temp2).not();
			}
		} else {
			Formula left = binaryTempFormula.left().accept(this);
			Formula right = binaryTempFormula.right().accept(this);
			return left.compose(binaryTempFormula.op(), right);
		}
	}
}
