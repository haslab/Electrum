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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;

import kodkod.ast.BinaryTempFormula;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.RelationPredicate;
import kodkod.ast.TempExpression;
import kodkod.ast.UnaryTempFormula;
import kodkod.ast.Variable;
import kodkod.ast.operator.TemporalOperator;
import kodkod.ast.visitor.AbstractReplacer;

/**
 * Translates an LTL temporal formula into its standard Kodkod FOL
 * representation. Assumes that the variable relations have been previously
 * expanded into its static version. To do so, it explicitly introduces the time
 * elements into the formula, converting the temporal operators into time
 * quantifiers and applying the time variable to variable relations. Since
 * global temporal quantifications force the trace to be infinite, the formula
 * must be in negative normal form to guarantee a correct translation.
 * 
 * @author Eduardo Pessoa, nmm (pt.uminho.haslab)
 */
public class LTL2FOLTranslator extends AbstractReplacer {

	/**
	 * The constraint forcing the time trace to be infinite. Forces the loop to
	 * exist.
	 */
	private final Formula infinite = TemporalTranslator.LOOP.one();

	/**
	 * Variables to handle the depth of nested post operators within the current
	 * temporal formula.
	 */
	private int currentPostDepth, maxPostDepth;

	/**
	 * The relations resulting from the extension of the variable relations.
	 * Should be provided to the constructor.
	 */
	private final Map<String, Relation> expandedRelations;

	/**
	 * Translates an LTL temporal formula into its standard Kodkod FOL
	 * representation, given the extension of the variable relations.
	 * 
	 * @param relations
	 *            the expanded static versions of the variable relations.
	 */
	public LTL2FOLTranslator(Map<String, Relation> expandedRelations) {
		super(new HashSet<Node>());
		this.expandedRelations = expandedRelations;
	}

	/**
	 * Converts an LTL temporal formula into a regular Kodkod FOL formula. Uses
	 * the visitor to convert and adds any trace constraint left at the top
	 * level to handle nested post operators. It also adds the constraints that
	 * define the structure of the time relation constants. This is the main
	 * method that should be called to convert temporal formulas. The formula
	 * should be in negative normal form in order for the temporal quantifiers
	 * to be correctly translated.
	 * 
	 * @param tempFormula
	 *            the LTL formula to be converted.
	 * @return the resulting FOL formula.
	 */
	public Formula translate(Formula tempFormula) {
		Formula order = TemporalTranslator.NEXT.totalOrder(TemporalTranslator.TIME, TemporalTranslator.INIT,
				TemporalTranslator.END);
		Formula loopDecl = TemporalTranslator.LOOP.partialFunction(TemporalTranslator.END, TemporalTranslator.TIME);
		Expression nextDecl = TemporalTranslator.NEXT.union(TemporalTranslator.LOOP);
		Formula nextFnct = TemporalTranslator.TRACE.eq(nextDecl);
		Formula structural = Formula.and(order, loopDecl, nextFnct);

		resetPostVariables();
		pushVariable();

		Formula result = tempFormula.accept(this).and(structural);
		if (maxPostDepth > 0)
			return forceNextExists(TemporalTranslator.INIT, maxPostDepth).and(result);
		else
			return result;
	}

	/**
	 * Converts an LTL temporal expression into a regular Kodkod FOL expression
	 * in a concrete time step, counting from the
	 * {@link TemporalTranslator#INIT initial} time. Uses the visitor to
	 * convert. This is the main method that should be called to convert
	 * temporal expressions.
	 * 
	 * @param tempExpression
	 *            the LTL expression to be converted.
	 * @return the resulting FOL formula.
	 */
	public Expression convert(Expression tempExpression, int state) {
		resetPostVariables();
		pushVariable(state);

		Expression result = tempExpression.accept(this);

		return result;
	}

	@Override
	public Expression visit(Relation relation) {
		maxPostDepth = currentPostDepth > maxPostDepth ? currentPostDepth : maxPostDepth;
		if (TemporalTranslator.isTemporal(relation))
			return expandedRelations.get(relation.name()).join(getVariable());
		else
			return relation;
	}

	@Override
	public Formula visit(RelationPredicate relationPredicate) {
		if (TemporalTranslator.isTemporal(relationPredicate))
			return relationPredicate.toConstraints().accept(this);
		else
			return relationPredicate;
	}

	@Override
	public Formula visit(UnaryTempFormula unaryTempFormula) {
		int temp = currentPostDepth;
		int tempM = maxPostDepth;
		resetPostVariables();
		pushOperator(unaryTempFormula.op());
		pushVariable();
		Formula e = unaryTempFormula.formula().accept(this);
		Formula rt = getQuantifier(getOperator(), e, maxPostDepth);
		popOperator();
		popVariable();
		currentPostDepth = temp;
		maxPostDepth = tempM;
		return rt;
	}

	@Override
	public Formula visit(BinaryTempFormula binaryTempFormula) {
		int temp = currentPostDepth;
		int tempM = maxPostDepth;

		pushOperator(binaryTempFormula.op());
		pushVariable();
		int quantificationPostRight, quantificationPostLeft, quantificationPostLeftf;
		Formula rt, left, right;
		switch (binaryTempFormula.op()) {
		case UNTIL:
			resetPostVariables();
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = maxPostDepth;
			pushVariable();
			resetPostVariables();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeftf = maxPostDepth;
			rt = getQuantifierUntil(left, right, quantificationPostLeftf, quantificationPostRight);
			popVariable();
			break;
		case RELEASE:
			resetPostVariables();
			Formula rightAlways = binaryTempFormula.right().accept(this);
			pushVariable();
			resetPostVariables();
			left = binaryTempFormula.left().accept(this);
			quantificationPostLeft = maxPostDepth;
			pushVariable();
			resetPostVariables();
			right = binaryTempFormula.right().accept(this);
			quantificationPostRight = maxPostDepth;
			rt = getQuantifierRelease(rightAlways, left, right, quantificationPostLeft, quantificationPostRight);
			popVariable();
			popVariable();
			break;
		default:
			throw new UnsupportedOperationException("Unsupported binary temporal operator:" + binaryTempFormula.op());
		}
		popVariable();
		popOperator();
		currentPostDepth = temp;
		maxPostDepth = tempM;
		return rt;
	}

	@Override
	public Expression visit(TempExpression tempExpression) {
		currentPostDepth++;
		pushOperator(tempExpression.op());
		pushVariable();
		// // condition to verify the number max of nested plicas!!
		// if (tempExpression.expression() instanceof TempExpression) {
		// numberMaxOfnestedPlicas++;
		// } else {
		// if (numberMaxOfnestedPlicas > needToDeclarePostR) {
		// needToDeclarePostR = numberMaxOfnestedPlicas;
		// numberMaxOfnestedPlicas = 1;
		// }
		// }
		//
		// // if the context is not a temporal operator.
		// if (getVariableLastQuantification() == init) {
		// if (numberMaxOfnestedPlicas > numberMaxPlicasInit) {
		// numberMaxPlicasInit = numberMaxOfnestedPlicas;
		// }
		// }
		Expression localExpression = tempExpression.expression().accept(this);
		popOperator();
		popVariable();
		currentPostDepth--;
		return localExpression;
	}

	private Formula getQuantifierUntil(Formula left, Formula right, int postDepthLeft, int postDepthRight) {
		Variable r = getVariableUntil(true);
		Variable l = getVariableUntil(false);
		Formula nfleft;
		// TODO: wrong, should use next rather than nextt
		if (postDepthLeft > 0) {
			nfleft = (forceNextExists(l, postDepthLeft).and(left)).forAll(l.oneOf(getVariableLastQuantificationUntil(
					false).join(TemporalTranslator.TRACE.reflexiveClosure()).intersection(
					TemporalTranslator.TRACE.closure().join(r))));
		} else {
			nfleft = left.forAll(l.oneOf(getVariableLastQuantificationUntil(false).join(
					TemporalTranslator.TRACE.reflexiveClosure()).intersection(
					TemporalTranslator.TRACE.closure().join(r))));
		}

		if (postDepthRight > 0) {
			return (forceNextExists(r, postDepthRight).and(right)).and(nfleft)
					.forSome(
							r.oneOf(getVariableLastQuantificationUntil(false).join(
									TemporalTranslator.TRACE.reflexiveClosure())));
		} else {
			return right.and(nfleft)
					.forSome(
							r.oneOf(getVariableLastQuantificationUntil(false).join(
									TemporalTranslator.TRACE.reflexiveClosure())));
		}
	}

	private Formula getQuantifierRelease(Formula always, Formula left, Formula right, int leftFormula, int rightFormula) {
		Variable r = getVariableRelease(true, false);
		Variable l = getVariableRelease(false, false);
		Variable v = getVariableRelease(false, true);
		Formula alw;
		Formula nfleft;
		Formula nfright;

		alw = infinite.and(always.forAll(v.oneOf(getVariableLastQuantificationRelease(false, true).join(
				TemporalTranslator.TRACE.reflexiveClosure()))));

		if (rightFormula > 0) {
			nfleft = (forceNextExists(l, rightFormula).and(right)).forAll(l.oneOf(getVariableLastQuantificationRelease(
					false, true).join(TemporalTranslator.TRACE.reflexiveClosure()).intersection(
					TemporalTranslator.TRACE.reflexiveClosure().join(r))));
		} else {
			nfleft = right.forAll(l.oneOf(getVariableLastQuantificationRelease(false, true).join(
					TemporalTranslator.TRACE.reflexiveClosure()).intersection(
					TemporalTranslator.TRACE.reflexiveClosure().join(r))));
		}

		if (leftFormula > 0) {
			nfright = (forceNextExists(r, leftFormula).and(left)).and(nfleft).forSome(
					r.oneOf(getVariableLastQuantificationRelease(false, true).join(
							TemporalTranslator.TRACE.reflexiveClosure())));
		} else {
			nfright = left.and(nfleft).forSome(
					r.oneOf(getVariableLastQuantificationRelease(false, true).join(
							TemporalTranslator.TRACE.reflexiveClosure())));
		}
		return alw.or(nfright);
	}

	private Formula getQuantifier(TemporalOperator op, Formula e, int posts) {
		Variable v;
		Expression quantification = getVariableLastQuantification();
		switch (op) {
		case ALWAYS:
			v = (Variable) getVariable();
			return infinite.and(e.forAll(v.oneOf(quantification.join(TemporalTranslator.TRACE.reflexiveClosure()))));
		case EVENTUALLY:
			v = (Variable) getVariable();
			if (posts > 0) {
				return forceNextExists(v, posts).and(e).forSome(
						v.oneOf(quantification.join(TemporalTranslator.TRACE.reflexiveClosure())));
			} else {
				return e.forSome(v.oneOf(quantification.join(TemporalTranslator.TRACE.reflexiveClosure())));
			}
		case HISTORICALLY:
			v = (Variable) getVariable();
			if (posts > 0) {
				return forceNextExists(v, posts).and(e).forAll(
						v.oneOf(quantification.join(TemporalTranslator.TRACE.transpose().reflexiveClosure())));
			} else {
				return e.forAll(v.oneOf(quantification.join(TemporalTranslator.TRACE.transpose().reflexiveClosure())));
			}
		case ONCE:
			v = (Variable) getVariable();
			if (posts > 0) {
				return forceNextExists(v, posts).and(e).forSome(
						v.oneOf(quantification.join(TemporalTranslator.TRACE.transpose().reflexiveClosure())));
			} else {
				return e.forSome(v.oneOf(quantification.join(TemporalTranslator.TRACE.transpose().reflexiveClosure())));
			}
		case NEXT:
		case PREVIOUS:
			Expression v1 = getVariable();
			if (posts > 0) {
				return forceNextExists(v1, posts).and(v1.some().and(e));
			} else {
				return v1.some().and(e);
			}
		default:
			return e;
		}
	}

	private Formula forceNextExists(Expression exp, int x) {
		Expression e = exp.join(TemporalTranslator.TRACE);
		for (int i = 1; i < x; i++) {
			e = e.join(TemporalTranslator.TRACE);
		}
		return e.some();
	}

	/**
	 * Resets the original values of the variable nested post operators
	 * accumulators. Should be called whenever a new temporal variable is
	 * quantified.
	 */
	private void resetPostVariables() {
		currentPostDepth = 0;
		maxPostDepth = 0;
	}

	/* Operators Context */
	private List<TemporalOperator> operators = new ArrayList<TemporalOperator>();

	private void pushOperator(TemporalOperator op) {
		operators.add(op);
	}

	private TemporalOperator getOperator() {
		return operators.get(operators.size() - 1);
	}

	// private boolean thereAreOperator() {
	// if (operators.size() == 0)
	// return false;
	// return true;
	// }

	private void popOperator() {
		operators.remove(operators.size() - 1);
	}

	/* Variables */
	private List<Expression> variables = new ArrayList<Expression>();
	private int totalVariablesIt = 0;

	// private void resetVariables() {
	// variables = new ArrayList<Expression>();
	// totalVar = 0;
	// }

	private void pushVariable() {
		if (!thereAreVariables()) {
			variables.add(TemporalTranslator.INIT);
			return;
		}

		switch (getOperator()) {
		case NEXT:
		case POST:
			variables.add(getVariable().join(TemporalTranslator.TRACE));
			break;
		case PREVIOUS:
			variables.add(getVariable().join(TemporalTranslator.TRACE.transpose()));
			break;
		default:
			Variable v = Variable.unary("t" + totalVariablesIt);
			variables.add(v);
			totalVariablesIt++;
		}
	}

	/**
	 * Used to initialize the translation at a time other than the initial one.
	 * 
	 * @param state
	 *            the step of the trace in which to start the translation.
	 */
	private void pushVariable(int state) {
		if (!thereAreVariables()) {
			Expression s = TemporalTranslator.INIT;
			for (int i = 0; i < state; i++)
				s = s.join(TemporalTranslator.TRACE);
			variables.add(s);
		} else
			throw new UnsupportedOperationException("vars");
	}

	private void popVariable() {
		variables.remove(variables.size() - 1);
	}

	private boolean thereAreVariables() {
		return !variables.isEmpty();
		// if (variables.size() == 0)
		// return false;
		// return true;
	}

	private Expression getVariable() {
		return variables.get(variables.size() - 1);
	}

	private Expression getVariableLastQuantification() {
		return variables.get(variables.size() - 2);
	}

	private Expression getVariableLastQuantificationUntil(boolean sideIsRight) {
		if (!sideIsRight) {
			return variables.get(variables.size() - 3);
		} else {
			return variables.get(variables.size() - 2);
		}
	}

	private Variable getVariableUntil(boolean sideIsRight) {
		if (!sideIsRight) {
			return (Variable) variables.get(variables.size() - 1);
		} else {
			return (Variable) variables.get(variables.size() - 2);
		}
	}

	private Expression getVariableLastQuantificationRelease(boolean sideIsRight, boolean isAlways) {
		if (isAlways) {
			return variables.get(variables.size() - 4);
		} else {
			if (!sideIsRight) {
				return variables.get(variables.size() - 3);
			} else {
				return variables.get(variables.size() - 2);
			}
		}
	}

	private Variable getVariableRelease(boolean sideIsRight, boolean isAlways) {
		if (isAlways) {
			return (Variable) variables.get(variables.size() - 3);
		} else {
			if (!sideIsRight) {
				return (Variable) variables.get(variables.size() - 1);
			} else {
				return (Variable) variables.get(variables.size() - 2);
			}
		}
	}

}
