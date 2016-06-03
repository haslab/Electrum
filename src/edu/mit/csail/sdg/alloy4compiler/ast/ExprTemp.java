/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files
 * (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify,
 * merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES
 * OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 * LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF
 * OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 */

package edu.mit.csail.sdg.alloy4compiler.ast;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4.JoinableList;
import edu.mit.csail.sdg.alloy4.Pos;

/** Immutable; represents a quantified expression.
 *
 * It can have one of the following forms:
 *
 * <br>
 * <br>  ( always formula )
 * <br>  ( next formula )
 * <br>  ( eventually formula )
 * <br>
 *
 * <br> <b>Invariant:</b> type!=EMPTY => sub.mult==0
 */

public final class ExprTemp extends Expr {

   /** The operator (ALWAYS) */
   public final Op op;

   /** The body of the quantified expression. */
   public final Expr sub;

   /** Caches the span() result. */
   private Pos span;

   //=============================================================================================================//

   /** {@inheritDoc} */
   @Override public Pos span() {
      Pos p = span;
      // We intentionally do NOT merge the VAR's position into the span.
      // That allows us to control the highlighting of this component
      // simply by deciding this.pos and this.closingBracket
      if (p == null) span = (p = pos.merge(closingBracket).merge(sub.span()));
      return p;
   }

   //=============================================================================================================//

   /** {@inheritDoc} */
   @Override public void toString(StringBuilder out, int indent) {
      if (indent<0) {
         out.append('(').append(op).append(' ');
         if (!(sub instanceof ExprConstant) || ((ExprConstant)sub).op!=ExprConstant.Op.TRUE) {
        	 out.append(" | "); 
        	 sub.toString(out,-1);
         }
         out.append(')');
      } else {
         for(int i=0; i<indent; i++) { out.append(' '); }
         out.append("Quantification(").append(op).append(") of ");
         sub.toString(out, indent+2);
      }
   }

   //=============================================================================================================//

   /** Constructs a new quantified expression. */
   private ExprTemp (Pos pos, Pos closingBracket, Op op, Type type, Expr sub, boolean ambiguous, long weight, JoinableList<Err> errs) {
      super(pos, closingBracket, ambiguous, type, 0, weight, errs);
      this.op = op;
      this.sub = sub;
   }

   //=============================================================================================================//

   /** This class contains all possible quantification operators. */
   public enum Op {
      /** always formula       		*/  ALWAYS("always"),
      /** next formula      		*/  AFTER("after"),
      /** eventually formula       	*/  EVENTUALLY("eventually"),
      /** historically formula      */  HISTORICALLY("historically"),
      /** previous formula      	*/  PREVIOUS("previous"),
      /** once formula       		*/  ONCE("once");

      /** The constructor. */
      private Op(String label) { this.label = label; }

      /** The human readable label for this operator. */
      private final String label;

      /** Constructs a quantification expression with "this" as the operator.
       *
       * @param pos - the position of the "quantifier" in the source file (or null if unknown)
       * @param closingBracket - the position of the "closing bracket" in the source file (or null if unknown)
       * @param decls - the list of variable declarations (each variable must be over a set or relation)
       * @param sub - the body of the expression
       */
      public final Expr make(Pos pos, Pos closingBracket, Expr sub) {
         Type t = Type.FORMULA;
         sub = sub.typecheck_as_formula();
         boolean ambiguous = sub.ambiguous;
         JoinableList<Err> errs = emptyListOfErrors;
         if (sub.mult!=0) errs = errs.make(new ErrorSyntax(sub.span(), "Multiplicity expression not allowed here."));
         long weight = sub.weight;
        
         if (errs.isEmpty()) errs = sub.errors; // if the vars have errors, then the subexpression's errors will be too confusing, so let's skip them
         return new ExprTemp(pos, closingBracket, this, t, sub, ambiguous, weight, errs);
      }

      /** Returns the human readable label for this operator */
      @Override public final String toString() { return label; }
   }

   //=============================================================================================================//

   /** {@inheritDoc} */
   @Override public Expr resolve(Type unused, Collection<ErrorWarning> warns) {
      return this;
   }

   //=============================================================================================================//

   /** {@inheritDoc} */
   public int getDepth() {
      int max = sub.getDepth();
      return 1 + max;
   }

   /** {@inheritDoc} */
   @Override public final<T> T accept(VisitReturn<T> visitor) throws Err { return visitor.visit(this); }

   /** {@inheritDoc} */
   @Override public String getHTML() {
       StringBuilder sb = new StringBuilder("<b>").append(op).append("</b> ");
       return sb.append("... <i>").append(type).append("</i>").toString();
   }

   /** {@inheritDoc} */
   @Override public List<? extends Browsable> getSubnodes() {
      ArrayList<Browsable> ans = new ArrayList<Browsable>();
      ans.add(make(sub.span(), sub.span(), "<b>body</b>", sub));
      return ans;
   }
}
