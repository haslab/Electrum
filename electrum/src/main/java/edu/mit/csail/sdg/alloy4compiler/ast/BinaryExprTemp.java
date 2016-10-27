package edu.mit.csail.sdg.alloy4compiler.ast;

import edu.mit.csail.sdg.alloy4.*;
import kodkod.ast.BinaryFormula;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import static edu.mit.csail.sdg.alloy4compiler.ast.Type.EMPTY;

/**
 * @author Eduardo Pessoa, Nuno Macedo
 */
public class BinaryExprTemp extends Expr {

    /** The binary operator. */
    public final Op op;

    /** The left-hand-side expression. */
    public final Expr left;

    /** The right-hand-side expression. */
    public final Expr right;

    /** Caches the span() result. */
    private Pos span = null;

    //============================================================================================================//

    /** Constructs a new BinaryExprTemp node. */
    private BinaryExprTemp(Pos pos, Pos closingBracket, Op op, Expr left, Expr right, Type type, JoinableList<Err> errors) {
        super(pos,
                closingBracket,
                left.ambiguous || right.ambiguous,
                type,
                (op.isArrow && (left.mult==2 || right.mult==2))?2:0,
                left.weight + right.weight,
                errors);
        this.op = op;
        this.left = left;
        this.right = right;
    }

    //============================================================================================================//

    /** Returns true if we can determine the two expressions are equivalent; may sometimes return false. */
    @Override public boolean isSame(Expr obj) {
        while(obj instanceof ExprUnary && ((ExprUnary)obj).op==ExprUnary.Op.NOOP) obj=((ExprUnary)obj).sub;
        if (obj==this) return true;
        if (!(obj instanceof ExprBinary)) return false;
        BinaryExprTemp x = (BinaryExprTemp)obj;
        return op==x.op && left.isSame(x.left) && right.isSame(x.right);
    }

    //============================================================================================================//

    /** Convenience method that generates a type error with "msg" as the message,
     * and includes the left and right bounding types in the message.
     */
    private static ErrorType error(Pos pos, String msg, Expr left, Expr right) {
        return new ErrorType(pos, msg+"\nLeft type = "+left.type+"\nRight type = "+right.type);
    }

    //============================================================================================================//

    /** Convenience method that generates a type warning with "msg" as the message,
     * and includes the left and right bounding types in the message.
     */
    private ErrorWarning warn(String msg) {
        return new ErrorWarning(pos, msg
                +"\nLeft type = " + Type.removesBoolAndInt(left.type)
                +"\nRight type = " + Type.removesBoolAndInt(right.type));
    }

    //============================================================================================================//

    /** Convenience method that generates a type warning with "msg" as the message,
     * and includes the parent's relevance type, as well as the left and right bounding types in the message.
     */
    private ErrorWarning warn(String msg, Type parent) {
        return new ErrorWarning(pos, msg
                + "\nParent's relevant type = " + Type.removesBoolAndInt(parent)
                + "\nLeft type = " + Type.removesBoolAndInt(left.type)
                + "\nRight type = " + Type.removesBoolAndInt(right.type));
    }

    //============================================================================================================//

    /** {@inheritDoc} */
    @Override public Pos span() {
        Pos p = span;
        if (p==null) span = (p = pos.merge(closingBracket).merge(right.span()).merge(left.span()));
        return p;
    }

    //============================================================================================================//

    /** {@inheritDoc} */
    @Override public void toString(StringBuilder out, int indent) {
        if (indent<0) {
            left.toString(out,-1); out.append(' ').append(op).append(' ');
            right.toString(out,-1);
        } else {
            for(int i=0; i<indent; i++) { out.append(' '); }
            out.append(op).append(" with type=").append(type).append('\n');
            left.toString(out, indent+2);
            right.toString(out, indent+2);
        }
    }

    //============================================================================================================//

    /** This class contains all possible binary operators. */
    public static enum Op {
        /** release formula   */  RELEASE("release",false),
        /** until formula   */    UNTIL("until",false);

        /** The constructor.
         * @param label - the label (for printing debugging messages)
         * @param isArrow - true if this operator is one of the 17 arrow operators
         */
        private Op(String label, boolean isArrow) {
            this.label=label;
            this.isArrow=isArrow;
        }

        /** The human readable label for this operator. */
        private final String label;

        /** True if and only if this operator is the Cartesian product "->", a "seq" multiplicity,
         * or is a multiplicity arrow of the form "?->?".
         */
        public final boolean isArrow;

        /** Constructs a new ExprBinary node.
         * @param pos - the original position in the source file (can be null if unknown)
         * @param left - the left hand side expression
         * @param right - the right hand side expression
         */
        public final Expr make(Pos pos, Pos closingBracket, Expr left, Expr right) {
            left = left.typecheck_as_formula();
            right = right.typecheck_as_formula();
            JoinableList<Err> errs = left.errors.make(right.errors);
            Err e=null;
            Type type=Type.FORMULA;;
           return new BinaryExprTemp(pos, closingBracket, this, left, right, type, errs.make(e));
        }

        /** Returns the human readable label for this operator. */
        @Override public final String toString() { return label; }

        /** Returns the human readable label already encoded for HTML */
        public final String toHTML() { return "<b>" + Util.encode(label) + "</b>"; }
    }

    //============================================================================================================//

    /** {@inheritDoc} */
    @Override public Expr resolve(Type p, Collection<ErrorWarning> warns) {
        if (errors.size()>0) return this;
        ErrorWarning w=null;
        Type a=left.type, b=right.type;

        Expr left = this.left.resolve(a, warns);
        Expr right = this.right.resolve(b, warns);

        if (w!=null) warns.add(w);
        return (left==this.left && right==this.right) ? this : op.make(pos, closingBracket, left, right);
    }

    //============================================================================================================//

    /** {@inheritDoc} */
    public int getDepth() {
        int a=left.getDepth(), b=right.getDepth();
        if (a>=b) return 1+a; else return 1+b;
    }

    /** {@inheritDoc} */
    @Override public final<T> T accept(VisitReturn<T> visitor) throws Err { return visitor.visit(this); }

    /** {@inheritDoc} */
    @Override public String getHTML() { return op.toHTML() + " <i>" + type + "</i>"; }

    /** {@inheritDoc} */
    @Override public List<? extends Browsable> getSubnodes() { return Util.asList(left, right); }

}
