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

package edu.mit.csail.sdg.alloy4compiler.translator;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.*;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary.Op;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;

/** Translate an Alloy AST into Kodkod AST then attempt to solve it using Kodkod. */

public final class TranslateTAlloyToInit extends VisitReturn<Expr> {

	private final Command command;
	public Iterable<Sig> old_sigs;
	public Expr expr = ExprConstant.TRUE;
	private final A4Reporter rep;
		
	public TranslateTAlloyToInit(A4Reporter rep, Command c, Iterable<Sig> old_sigs) throws Err {
		this.command = c;
		this.old_sigs = old_sigs;
		this.rep = rep;
	}
	
	public Command untemp() throws Exception {
		for (Sig s : old_sigs) 
			convertFacts(s);
//		rep.debug("ORIGINAL: "+command.formula);
		expr = visitThis(command.formula);
		rep.debug("\nNEWINITFACT: "+expr);
		rep.debug("\nMaxTime: "+command.time);
		Command cmd = new Command(command.check, command.overall, command.bitwidth, command.maxseq, command.time, command.timeexact, expr);
		cmd = cmd.change(command.scope);
		rep.debug("\nScope: "+cmd.scope);
		return cmd;
	}
	
	@Override
	public Expr visit(ExprBinary x) throws Err {
		Expr a = (Expr) x.left.accept(this);
		Expr b = (Expr) x.right.accept(this);
		return x.op.make(x.pos, x.closingBracket, a, b);
	}

	@Override
	public Expr visit(ExprList x) throws Err {
		List<Expr> a = new ArrayList<Expr>();
		for (Expr y : x.args) 
			try {
				a.add(y.accept(this));
			}
		catch (UnsupportedOperationException e) {}
		return ExprList.make(x.pos, x.closingBracket, x.op, a);
	}

	@Override
	public Expr visit(ExprCall x) throws Err {
		List<Expr> args_new = new ArrayList<Expr>();
		for (Expr a : x.args)
			args_new.add(a.accept(this));
		Expr converted_return = x.fun.returnDecl.accept(this);
		Expr converted_body = x.fun.getBody().accept(this);
		Func  f = new Func(x.fun.pos, x.fun.label, x.fun.decls, converted_return, converted_body);
		return f.call(args_new.toArray(new Expr[args_new.size()]));
	}

	@Override
	public Expr visit(ExprConstant x) throws Err {
		return x;
	}

	@Override
	public Expr visit(ExprITE x) throws Err {
		Expr cond = x.cond.accept(this);
		Expr left = x.left.accept(this);
		Expr right = x.right.accept(this);
		return x;
	}

	@Override
	public Expr visit(ExprLet x) throws Err {
		throw new UnsupportedOperationException("Temporal: "+x);
	}

	@Override
	public Expr visit(ExprQt x) throws Err {
		for (Decl d : x.decls) {
			Expr b = (Expr) d.expr.accept(this);
		}
		Expr a = null;
		
		a = (Expr) x.sub.accept(this);
		return x.op.make(x.pos, x.closingBracket, x.decls, a)	;
	}

	@Override
	public Expr visit(BinaryExprTemp x) throws Err {
		return null;
	}

	@Override
	public Expr visit(ExprUnary x) throws Err {
		Expr res = null;
		if (x.op == Op.POST) {
			throw new UnsupportedOperationException("Temporal: "+x);
		}
		Expr a = x.sub.accept(this);
		return x.op.make(x.pos, a);
	}

	@Override
	public Expr visit(ExprVar x) throws Err {
		return x;
	}

	private void convertFacts(Sig old_sig) throws Err {

		Expr old_block = ExprConstant.TRUE;
		
		for (Expr e: old_sig.getFacts())
			old_block = old_block.and(e);
		old_sig.clearFacts();
		if (!ExprConstant.TRUE.isSame(old_block)) {
			Expr new_block = old_block.accept(this);
			old_sig.addFact(new_block);
		}
		
	}
	
	@Override
	public Expr visit(Field x) throws Err {
		return x;
//		if (x.isVariable != null) return x;
//		else throw new UnsupportedOperationException("Temporal: "+x);
	}

	@Override
	public Expr visit(ExprTemp x) throws Err {
		throw new UnsupportedOperationException("Temporal: "+x);
	}

	@Override
	public Expr visit(Sig x) throws Err {
		return x;
//		if (x.isVariable != null) return x;
//		else throw new UnsupportedOperationException("Temporal: "+x);
	}


}

