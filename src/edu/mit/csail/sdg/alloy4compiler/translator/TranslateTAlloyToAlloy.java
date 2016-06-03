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
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4compiler.ast.Attr;
import edu.mit.csail.sdg.alloy4compiler.ast.Attr.AttrType;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.CommandScope;
import edu.mit.csail.sdg.alloy4compiler.ast.Decl;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprITE;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprLet;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprQt;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprTemp;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.Type;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary.Op;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.SubsetSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Type.ProductType;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitReturn;
import edu.mit.csail.sdg.alloy4compiler.parser.CompModule.Open;

/** Translate an Alloy AST into Kodkod AST then attempt to solve it using Kodkod. */

// TODO: LET expressions are not supported
// TODO: PRIME occurrences should check for the existence of the next instance
// TODO: as a consequence, nested PRIMES should be forbidden

public final class TranslateTAlloyToAlloy extends VisitReturn<Expr> {

	private Pair<Expr,Expr> current_state;
	private final Command command;
	public Map<ExprHasName,Expr> vars = new HashMap<ExprHasName,Expr>();
	public Map<String,Sig> new_sigs = new HashMap<String,Sig>();
	private Map<String,Map<String,Field>> fields = new HashMap<String,Map<String,Field>>();
	public Iterable<Sig> old_sigs;
	public Expr expr = ExprConstant.TRUE;
	private boolean negated = false;
	private boolean post = false;
	private final Expr finite,infinite;
	private final A4Reporter rep;
		
	public TranslateTAlloyToAlloy(A4Reporter rep, Command c, Iterable<Sig> old_sigs) throws Err {

		this.command = c;
		this.old_sigs = old_sigs;
		this.rep = rep;
		new_sigs.put(PrimSig.TIME.label, PrimSig.TIME);
		// create order for states
		List<Expr> x = new ArrayList<Expr>();
		x.add(PrimSig.TIME);
		

		//lone sig back in elem {}
		List<Sig> y = new ArrayList<Sig>();
		y.add(PrimSig.TIME);
		//pred finite { no loop }
		finite = ExprConstant.LOOP.no();
		//pred infinite { some loop }
//		expr = (ExprConstant.END.join(ExprConstant.NEXTTIME).some()).iff(ExprConstant.LOOP.some());
//		infinite = ((ExprConstant.LOOP.one()).and(ExprConstant.END.join(ExprConstant.NEXTTIME).one()).and(ExprConstant.LOOP.in(ExprConstant.NEXTTIME)));
		expr = (ExprConstant.END.join(ExprConstant.NEXTTIME).some()).iff(ExprConstant.LOOP.some()).and(ExprConstant.LOOP.in(ExprConstant.NEXTTIME)).and(ExprConstant.END.join(ExprConstant.NEXTTIME).lone());
		infinite = ExprConstant.LOOP.one();
		// by default, the context time is the first one
		setCurrentState(ExprConstant.INIT);
//		rep.debug("infinite: "+ExprConstant.LOOP.some());

	}
	
	public Command untemp() throws Exception {
   	 	if (command.time < 1) throw new ErrorFatal("Time scope must be defined.");

		for (Sig s : old_sigs)
			convertSig(s);
		// rep.debug("Survived");
		for (Sig s : old_sigs)
			if (!s.builtin) convertFacts(s);
		// negated = command.check;
		 rep.debug("ORIGINAL: "+command.formula);
		expr = expr.and(visitThis(command.formula));
		
//		for (String a : new_sigs.keySet()) {
//			rep.debug(a + "::\n ");
//			for (Field f : new_sigs.get(a).getFields())
//				rep.debug("\t" + f.label + ":" + f.type() + "\n");
//			for (Expr f : new_sigs.get(a).getFacts())
//				rep.debug("\t" + f + "\n");
//			rep.debug("--------");
//		}
		rep.debug("\nFACT: " + expr);
//		rep.debug("\nMaxTime: " + command.time);

		List<CommandScope> scopes = new ArrayList<CommandScope>();
		for (CommandScope scope : command.scope) {
			CommandScope new_scope = new CommandScope(scope.pos, new_sigs.get(scope.sig.label), scope.isExact,
					scope.startingScope, scope.endingScope, scope.increment);
			scopes.add(new_scope);
		}

		List<Sig> additional = new ArrayList<Sig>();
		for (Sig scope : command.additionalExactScopes)
			additional.add(new_sigs.get(scope.label));

		Command cmd = new Command(command.pos, command.label, command.check, command.overall, command.bitwidth,
				command.maxseq, command.time, command.timeexact, command.expects, scopes, additional, expr,
				command.parent);
		rep.debug("\nScope: " + cmd.scope);
		return cmd;
	}
	
	@Override
	public Expr visit(ExprBinary x) throws Err {
//		rep.debug("In: "+x);
		Expr a = (Expr) x.left.accept(this);
		Expr b = (Expr) x.right.accept(this);
//		rep.debug("Ona: "+a);
//		rep.debug("Onb: "+b);
		if (negated) {
			if (x.op == ExprBinary.Op.AND)
				return ExprBinary.Op.OR.make(x.pos, x.closingBracket, a, b); 
			if (x.op == ExprBinary.Op.OR)
				return ExprBinary.Op.AND.make(x.pos, x.closingBracket, a, b); 
			if (x.op == ExprBinary.Op.IMPLIES) {
				negated = !negated;
				a = (Expr) x.left.accept(this);
				negated = !negated;
				return ExprBinary.Op.AND.make(x.pos, x.closingBracket, a, b); 
			}
			if (x.op == ExprBinary.Op.IFF) {
				negated = !negated;
				Expr a1 = (Expr) x.left.accept(this);
				Expr b1 = (Expr) x.right.accept(this);
				negated = !negated;
				Expr r1 = ExprBinary.Op.OR.make(x.pos, x.closingBracket, a, b);
				Expr r2 = ExprBinary.Op.OR.make(x.pos, x.closingBracket, a1, b1);
				return ExprBinary.Op.AND.make(x.pos, x.closingBracket, r1, r2); 
			}
			if (x.op == ExprBinary.Op.IN) return ExprBinary.Op.NOT_IN.make(x.pos, x.closingBracket, a, b);  
			if (x.op == ExprBinary.Op.NOT_IN) return ExprBinary.Op.IN.make(x.pos, x.closingBracket, a, b);  
			if (x.op == ExprBinary.Op.EQUALS) return x.op.make(x.pos, x.closingBracket, a, b).not();  
			return x.op.make(x.pos, x.closingBracket, a, b); 
		} else {
			return x.op.make(x.pos, x.closingBracket, a, b); 
		}
	}

	@Override
	public Expr visit(ExprList x) throws Err {
		List<Expr> a = new ArrayList<Expr>();
		for (Expr y : x.args) {
			a.add(y.accept(this));
		}
		if (negated) {
			if (x.op == ExprList.Op.AND) return ExprList.make(x.pos, x.closingBracket, ExprList.Op.OR, a);
			if (x.op == ExprList.Op.OR) return ExprList.make(x.pos, x.closingBracket, ExprList.Op.AND, a);
			throw new UnsupportedOperationException("Temporal: "+x);
		} else {
			return ExprList.make(x.pos, x.closingBracket, x.op, a);
		}
	}

	@Override
	public Expr visit(ExprCall x) throws Err {
		boolean temp = negated;
		if (!x.fun.isPred) negated = false;
		List<Expr> args_new = new ArrayList<Expr>();
		for (Expr a : x.args)
			args_new.add(a.accept(this));
		Expr converted_return = x.fun.returnDecl.accept(this);
		List<Decl> decls_new = new ArrayList<Decl>();
		int k = 0;
		for (int i = 0; i<x.fun.decls.size(); i++)
			for (int j = 0; j<x.fun.decls.get(i).names.size(); j++)
				vars.put(x.fun.decls.get(i).names.get(j), args_new.get(k++));
//		for (Decl d : x.fun.decls) {
//			if (!(d.expr instanceof ExprUnary)) throw new UnsupportedOperationException("Temporal: "+d.expr);
//			Expr b = convertSig((Sig) ((ExprUnary) d.expr).sub);
//			Decl d1 = new Decl(d.isPrivate, d.disjoint, d.disjoint2, d.names, b.oneOf());
//			vars.put(d.get(),d1.get());
//			decls_new.add(d1);
//		}
		Expr converted_body = x.fun.getBody().accept(this);
		negated = temp;
//		Func func_converted = new Func(x.fun.pos, x.fun.isPrivate, x.fun.label, decls_new, converted_return, converted_body);
//		Expr res = func_converted.call(args_new.toArray(new Expr[args_new.size()]));
		return converted_body;
	}

	@Override
	public Expr visit(ExprConstant x) throws Err {
		return negated?x.not():x;
	}

	@Override
	public Expr visit(ExprITE x) throws Err {
		Expr aux;
		if (x.left.type() != Type.FORMULA) {
			Expr a = (Expr) x.left.accept(this);
			Expr b = (Expr) x.right.accept(this);
			Expr c = (Expr) x.cond.accept(this);
			aux = ExprITE.make(x.pos, c, a, b);
		}
		else {
			aux = (x.cond.and(x.left)).or(x.cond.not().and(x.right)).accept(this);
		}
		return aux;
	}

	@Override
	public Expr visit(ExprLet x) throws Err {
		throw new UnsupportedOperationException("Temporal: "+x);
	}

	@Override
	public Expr visit(ExprQt x) throws Err {
		List<Decl> decls_new = new ArrayList<Decl>();
		for (Decl d : x.decls) {
			Expr b = (Expr) d.expr.accept(this);
			Decl d1 = new Decl(null, d.isPrivate, d.disjoint, d.disjoint2, d.names, b);
			for (int i = 0; i<d.names.size(); i++) {
				vars.put(d.names.get(i), d1.names.get(i));
			}
			decls_new.add(d1);
		}
		Expr a = null;
		if (negated) {
			if (x.op == ExprQt.Op.ALL) {
				a = (Expr) x.sub.accept(this);
				return ExprQt.Op.SOME.make(x.pos, x.closingBracket, decls_new, a); 
			}
			if (x.op == ExprQt.Op.SOME) {
				a = (Expr) x.sub.accept(this);
				return ExprQt.Op.ALL.make(x.pos, x.closingBracket, decls_new, a); 
			}
			if (x.op == ExprQt.Op.NO) {
				boolean old = negated;
				negated = false;
				a = (Expr) x.sub.accept(this);
				Expr xx = ExprQt.Op.SOME.make(x.pos, x.closingBracket, decls_new, a); 
				negated = old;
				return xx;
			}
			throw new UnsupportedOperationException("Temporal: "+x);
		} else {
			a = (Expr) x.sub.accept(this);
			return x.op.make(x.pos, x.closingBracket, decls_new, a); 
		}
	}

	@Override
	public Expr visit(ExprUnary x) throws Err {
		Expr res = null;
		if (x.op == Op.NOT) {
			negated = !negated;
			res = x.sub.accept(this);
			negated = !negated;
		} else if (x.op == Op.POST) {
			boolean temp = post;
			post = true;
			res = x.sub.accept(this);
			post = temp;
		} else if (negated && (x.op == Op.LONE || x.op == Op.NO || x.op == Op.SOME || x.op == Op.ONE)) {
			negated = !negated;
			Expr a = x.sub.accept(this);
			res = x.op.make(x.pos, a).not();		
			negated = !negated;
		} else {
			Expr a = x.sub.accept(this);
			res = x.op.make(x.pos, a);
		}
		return res;
	}

	@Override
	public Expr visit(ExprVar x) throws Err {
		// variables should have already been converted by the quantifier
		if (vars.get(x) == null) 
			throw new ErrorFatal("Variable not translated: "+x);
		return vars.get(x);
//		Expr type_converted = null;
//		for (ProductType t : x.type()) {
//			for (int i = 0; i<t.arity(); i ++)
//				type_converted = (type_converted==null)? sigs.get(t.get(i).label) : type_converted.product(sigs.get(t.get(i).label));
//		}
//		return ExprVar.make(x.pos, x.label, type_converted.type());
	}

	private Sig convertSig(Sig old_sig) throws Err {
//		rep.debug("Started: "+old_sig.label+" with "+old_sig.getFields());

		if (old_sig.builtin) {
			// built-in sigs are static
			new_sigs.put(old_sig.label, old_sig);
//			rep.debug("Built-in: "+old_sig.label);
			return old_sig;
		}
		else {
			// test whether the sig has already been converted
			Sig sig_new = new_sigs.get(old_sig.label);
			if(sig_new != null) {
//				rep.debug("Already: "+old_sig.label);
				return sig_new;
			}
//			rep.debug("In0: "+old_sig.label);

			ArrayList<Attr> as1 = new ArrayList<Attr>();

			for (Attr a : old_sig.attributes)
				if (a != null && !(old_sig.isVariable != null && (a.type.equals(AttrType.ONE) || a.type.equals(AttrType.SOME) || a.type.equals(AttrType.LONE))))
					as1.add(a);
			
			Attr[] as = (Attr[]) as1.toArray(new Attr[as1.size()]);
			
			// create new sig with converted hierarchy
			if (old_sig instanceof PrimSig) {
//				rep.debug("In1:");
//				rep.debug("In1: "+old_sig.label);
				PrimSig parent_old = (PrimSig) ((PrimSig)old_sig).parent;
//				rep.debug("In2: "+old_sig.label);
				PrimSig parent_new = (PrimSig) (parent_old == null? null : convertSig(parent_old));				
//				rep.debug("In3: "+old_sig.label);
				sig_new = new PrimSig(old_sig.label,parent_new,as);
			} else {
				Set<Sig> parents_new = new HashSet<Sig>();
				for (Sig parent_old : ((SubsetSig) old_sig).parents)
					parents_new.add(convertSig(parent_old));				
				sig_new = new SubsetSig(old_sig.label, parents_new, as);
			}
//			rep.debug("Back to "+old_sig.label);

			new_sigs.put(sig_new.label, sig_new);
			// to convert the "this" variable
			vars.put(old_sig.decl.get(), sig_new.decl.get());
//			rep.debug("In4: "+old_sig.label);

			// adds the state field
			if (old_sig.isVariable != null) {
				if (fields.get(old_sig.label) == null) {
					Map<String,Field> fs = new HashMap<String,Field>();
					fs.put(old_sig.label,sig_new.addField("_"+old_sig.toString(), PrimSig.TIME.setOf()));
					fields.put(old_sig.label, fs);
				}		
			}
//			rep.debug("In5: "+old_sig.label);

			for (Field old_field : old_sig.getFields()) {
				Pair<Expr,Expr> temp = current_state;
				Decl state_decl = PrimSig.TIME.oneOf("s");
				setCurrentState(state_decl.get());
				Expr new_bound = (Expr) old_field.decl().expr.accept(this);
				Expr new_type = null;

				for (ProductType t : old_field.type()) {
					for (int i = 1; i<t.arity(); i ++)
						new_type = (new_type==null)? new_sigs.get(t.get(i).label) : new_type.product(new_sigs.get(t.get(i).label));
				}

//		        rep.debug("new bound: "+new_bound.toString());

//		        rep.debug("is var: "+old_field.isVariable);

				Field nf;
				Expr bound_converted_state = null;
				if (old_field.type().arity() == 2) {
					switch (((ExprUnary) new_bound).op) {
						case ONEOF  : bound_converted_state = old_sig.accept(this).any_arrow_one(((ExprUnary)new_bound).sub); break;
						case SETOF  : bound_converted_state = old_sig.accept(this).product(((ExprUnary)new_bound).sub); break;
						case SOMEOF : bound_converted_state = old_sig.accept(this).any_arrow_some(((ExprUnary)new_bound).sub); break;
						case LONEOF : bound_converted_state = old_sig.accept(this).any_arrow_lone(((ExprUnary)new_bound).sub); break;
						default		: bound_converted_state = old_sig.accept(this).product(((ExprUnary)new_bound).sub); break;
					}
				}
				else {
					bound_converted_state = old_sig.accept(this).product(new_bound);
				}

				if (old_field.isVariable != null) { 

					nf = sig_new.addField(old_field.label,new_type.product(PrimSig.TIME));
//					Expr fact = ((sig_new.decl.get().join(nf.join(state_decl.get()))).in(new_bound)).forAll(state_decl);
//					sig_new.addFact(fact);
					sig_new.addFact(nf.join(state_decl.get()).in(bound_converted_state).forAll(state_decl));
					rep.debug("field: "+nf.in(bound_converted_state).forAll(state_decl));
				}
				else {
					nf = sig_new.addField(old_field.label,new_bound);
//					Expr fact = ((sig_new.decl.get().join(nf)).in(new_bound)).forAll(state_decl);
//					sig_new.addFact(fact);
					sig_new.addFact(nf.in(bound_converted_state).forAll(state_decl));
				}

				if (fields.get(old_sig.label) == null) {
					Map<String,Field> fs = new HashMap<String,Field>();
					fields.put(old_sig.label, fs);
				}		

				fields.get(old_sig.label).put(old_field.label,nf);
				current_state = temp;
			}
//			rep.debug("In6: "+old_sig.label);

			
			
//			rep.debug("Finished: "+old_sig.label);
//			rep.debug("In9: "+old_sig.label);

			return sig_new;
		}
	}

	private void convertFacts(Sig old_sig) throws Err {
//		rep.debug("Started: "+old_sig.label+" with "+old_sig.getFields());

		Sig sig_new = new_sigs.get(old_sig.label);
		// create a new temporal context
		Pair<Expr,Expr> temp = current_state;
		Decl state_decl = PrimSig.TIME.oneOf("s");;
		setCurrentState(state_decl.get());

		Expr mult = null;
		// get the multiplicity fact
		// optimization: may be preserved as multiplicity attribute if not var
		// cannot be added to the signature fact due to empty "this" quantifications
		if (old_sig.isLone!=null)
			mult = (old_sig.lone());
		if (old_sig.isSome!=null)
			mult = (old_sig.some());
		if (old_sig.isOne!=null) 
			mult = (old_sig.one());
//		rep.debug("In8: "+old_sig.label);


		if (mult != null)
			expr = expr.and((mult.accept(this)).forAll(state_decl));
		

		if (old_sig.isVariable != null) state_decl = ((sig_new.decl.get().join(fields.get(old_sig.label).get(old_sig.label)))).oneOf("s");
		setCurrentState(state_decl.get());

		
		Expr old_block = ExprConstant.TRUE;
		
		// get the optional constraint block
		for (Expr e: old_sig.getFacts())
			old_block = old_block.and(e);
		
		
//		rep.debug("In7: "+old_sig.label);

		if (old_sig instanceof PrimSig) {
			Expr children_old = Sig.NONE;
			for (Sig s: ((PrimSig) old_sig).children())
				children_old = children_old.plus(s);
			
			// get the hierarchy fact
			// optimization: unnecessary if var
			if (!Sig.NONE.isSame(children_old))
				old_block = old_block.and(children_old.in(old_sig));

			// get the abstract fact
     		// optimization: unnecessary if no var child
			if (sig_new.isAbstract!=null && !Sig.NONE.isSame(children_old))
				old_block = old_block.and(old_sig.in(children_old));
		}

		
		rep.debug("S: "+expr);

		// convert the whole block
		if (!ExprConstant.TRUE.isSame(old_block)) {
//			rep.debug("old block: "+old_block.toString());
			Expr new_block = old_block.accept(this);
			sig_new.addFact((new_block).forAll(state_decl));
//	        rep.debug("new block: "+new_block.toString());
		}
		
		current_state = temp;
	}
	
	@Override
	public Expr visit(Field x) throws Err {
		Field xt = fields.get(x.sig.label).get(x.label);
		if (x.isVariable != null) {
			Expr aux =  xt.join(post?current_state.b:current_state.a);
			return aux;
		}
		else return xt;
	}

	@Override
	public Expr visit(ExprTemp x) throws Err {
		Pair<Expr,Expr> temp = current_state;
		Expr res = null;
		if (x.op.equals(ExprTemp.Op.AFTER)) {
			setCurrentState(current_state.b);
			res = ((Expr) x.sub.accept(this)).and(current_state.a.some());
		} else {
			Decl d = current_state.a.join(ExprConstant.NEXTTIME.reflexiveClosure()).oneOf(current_state.a.toString()+"'");
//			rep.debug("CURRENT STATE: "+current_state.a);
			setCurrentState(d.get());
			Expr xx = (Expr) x.sub.accept(this);
			switch (x.op) {
				case ALWAYS:     res = negated?
						(xx.forSome(d)):
						(xx.forAll(d)).and(infinite);
						break;
				case EVENTUALLY: res = negated?
						(xx.forAll(d)).and(infinite):
						(xx.forSome(d));
						break;
				default: 		 res = xx;
			}
		}
		current_state = temp;
		return res;
	}

	@Override
	public Expr visit(Sig x) throws Err {
		Sig xt = convertSig(x);
		if (xt.isVariable != null) return fields.get(xt.label).get(xt.label).join(post?current_state.b:current_state.a);
		else return xt;
	}
	
	private void setCurrentState(Expr s) {
		current_state = new Pair<Expr,Expr>(s,s.join(ExprConstant.NEXTTIME));
	}
}

