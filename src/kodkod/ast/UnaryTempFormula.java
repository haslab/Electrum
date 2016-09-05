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
package kodkod.ast;

import kodkod.ast.operator.TemporalOperator;
import kodkod.ast.visitor.ReturnVisitor;
import kodkod.ast.visitor.VoidVisitor;

/**
 * Temporal formula class
 * @author Eduardo Pessoa, nmm
 * pt.uminho.haslab
 */
public final class UnaryTempFormula extends Formula {
    private final Formula formula;
    private final TemporalOperator temporalOperator;

    UnaryTempFormula(TemporalOperator op, Formula child) {
        if (!op.unary()) {
            throw new IllegalArgumentException("Not a unary operator: " + op);
        }
        if (op == null || child == null) {
            throw new NullPointerException("null arg");
        }
        this.formula = child;
        this.temporalOperator = op;
    }

    public Formula formula() { return formula; }

    public TemporalOperator op() { return temporalOperator; }

    public <E, F, D, I> F accept(ReturnVisitor<E, F, D, I> visitor) {
        return visitor.visit(this);
    }

    public void accept(VoidVisitor visitor) {
        visitor.visit(this);
    }

    public String toString() {
    	return this.temporalOperator + "(" + formula + ")";
    }
}
