package edu.mit.csail.sdg.alloy4compiler.parser;

import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.NONE;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Attr;
import edu.mit.csail.sdg.alloy4compiler.ast.Decl;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBadCall;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBadJoin;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprHasName;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprList;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.VisitQuery;
import edu.mit.csail.sdg.alloy4compiler.translator.ConvToConjunction;

// - create an abstract sig Action
// - for each action, create sig extending sig Action
// - for each action, create pre- and post-condition predicates (args = action args)
// - collect the types of the arguments of every action
// - create a singleton argument Dummy
// - create abstract sig Arg to equal all argument types plus Dummy
// - create field event from every action to padded arguments (considering maximum num of args)
// - create singleton sig E with field event
// - create fired predicate with args action plus max number of arguments based on field event
// - for each action, create firing condition, relating predicate with pre-/post-conditions
// - for each action, create the firing predicate calling the fired predicate
// - for each modified elem, create FC relating modification to fired predicate
// - for the remainder, force unchanged

/**
 * Expands expression in the action idiom into regular Alloy.
 * 
 * @author Nuno Macedo
 */
public class Action2Alloy {

	/** the arguments of each defined action */
	private Map<String,List<Decl>> acts_args = new HashMap<String, List<Decl>>();
	/** the actions that modify each element */
	private Map<String, List<Sig>> acts_mods = new HashMap<String, List<Sig>>();

	public void expand(final A4Reporter rep, final CompModule root, LinkedHashMap<Sig, List<Decl>> old2fields) throws Err {
		if (acts_args.isEmpty()) return;
		
		// create the parent Action signature
		Sig action_sig = root.addSig("_Action", null, null, null, null, Attr.ABSTRACT, Attr.PRIVATE);
//		System.out.println("Created sig "+action_sig.label+" with "+action_sig.attributes+".");
		// create the Dummy argument signature
		Sig dummy_sig = root.addSig("_Dummy", null, null, null, null, Attr.ONE, Attr.PRIVATE);
//		System.out.println("Created sig "+dummy_sig.label+" with "+dummy_sig.attributes+".");
		
		final ExprVar dummy_var = ExprVar.make(null, dummy_sig.label);
		final ExprVar action_var = ExprVar.make(null, action_sig.label);
		
		// calculate maximum number of arguments and the set of different argument types
		List<ExprVar> args = new ArrayList<ExprVar>();
		args.add(dummy_var);
		int max_args = 0;
		for (List<Decl> ds : acts_args.values()) {
			if (ds.size() > max_args) max_args = ds.size();
			for (Decl d : ds) {
				if (!(d.expr instanceof ExprVar)) throw new ErrorSyntax("Bad action arg.");
				if (d.names.size()>1) throw new ErrorSyntax("Bad action arg.");
				args.add((ExprVar) d.expr);
			}
		}
		// define sig Arg as the sum of all argument types
		// TODO: avoid repeated arg types
		Sig arg_sig = root.addSig("_Arg", ExprVar.make(null,"="), args, null, null, Attr.PRIVATE, Attr.VARIABLE);
//		System.out.println("Max args is "+max_args+", sig "+arg_sig.label+" defined = "+ ((SubsetSig) arg_sig).parents + " with "+arg_sig.attributes+".");	

		final ExprVar arg_var = ExprVar.make(null, arg_sig.label);

		// for each action, calculate the type expression padded with dummies
		Expr padded_act_types = NONE;
		for (int i = 0; i < max_args; i++)
			padded_act_types = padded_act_types.product(NONE);
		for (String act_name : acts_args.keySet()) {
			Expr expr_aux = ExprVar.make(null, actSigName(act_name));
			for (int i = 0; i < max_args; i++) {
				Expr expr_cur;
				if (i>=(acts_args.get(act_name).size()))
					expr_cur = dummy_var;
				else {
					String n = "this/"+((ExprVar) acts_args.get(act_name).get(i).expr).label;
					expr_cur = ExprVar.make(null,n);
				}
				expr_aux = expr_aux.product(expr_cur);
			}
			padded_act_types = padded_act_types.plus(expr_aux);
		}
		
		// create the sig E and field events with type from each action sig to the padded type
		List<ExprHasName> ev_names = new ArrayList<ExprHasName>();
		ev_names.add(ExprVar.make(null, "_event"));
		Expr ev_expr = padded_act_types;
		Decl ev = new Decl(Pos.UNKNOWN, Pos.UNKNOWN, null, null, ev_names, ev_expr);
//		System.out.println("Field "+ev_names.get(0)+ " defined with "+ ev_expr+".");	
		
		List<Decl> fields = new ArrayList<Decl>();
		fields.add(ev);
		Sig e_sig = root.addSig("_E", null, null, fields, null, Attr.ONE, Attr.PRIVATE);
//		System.out.println("Created sig "+e_sig.label+" with "+e_sig.attributes+".");

		final ExprVar e_var = ExprVar.make(null, e_sig.label);

		Expr mult = e_var.join(ExprVar.make(null, "_event")).one().always();
		root.addFact(null, "_e_mult", mult);
//		System.out.println("Added event multiplicity fact: "+mult+".");

		
		// create the arguments for the fired predicate, action + args
		List<Decl> fired_args = new ArrayList<Decl>();
		// create the action argument arguments
		List<ExprHasName> args_decls_names = new ArrayList<ExprHasName>();
		if (max_args>0) {
			for (int i = 0; i < max_args; i++)
				args_decls_names.add(ExprVar.make(null,"_x"+i));
			fired_args.add(new Decl(null, null, null, null, args_decls_names, arg_var));
		}

		// create the action argument
		List<ExprHasName> act_decl_names = new ArrayList<ExprHasName>();
		final ExprVar act_arg = ExprVar.make(null,"_a"); 
		act_decl_names.add(act_arg);
		fired_args.add(new Decl(null, null, null, null, act_decl_names, action_var));

		// create the body for the fired predicate
		Expr fired_expr = act_arg;
		for (int i = 0; i < max_args; i++)
			fired_expr = fired_expr.product(args_decls_names.get(i));
		fired_expr = fired_expr.in(e_var.join(ev_names.get(0)));
		
		// create the fired predicate
		final String fired_name = "_fired";
		root.addFunc(null, null, fired_name, null, fired_args, null, fired_expr);
//		System.out.print("Created predicate "+fired_name+" with ");
//		for (Decl d : fired_args) System.out.print(d.names+":"+d.expr+" ");
//		System.out.println("as "+fired_expr+".");

		final ExprVar fired_var = ExprVar.make(null, fired_name);

		// for each action, create the fired condition		
		for (String act_name : acts_args.keySet()) {
			List<Expr> fire_args = new ArrayList<Expr>();
			Expr pre = ExprVar.make(null, prePredName(act_name));
			Expr post = ExprVar.make(null, postPredName(act_name));
			Expr fir = fired_var;
			Decl[] fire_decls = new Decl[acts_args.get(act_name).size()];
			for (int i = 0; i < acts_args.get(act_name).size(); i++) {
				Decl dcl = acts_args.get(act_name).get(i);
				fire_decls[i] = dcl;
				Expr e = ExprVar.make(null, dcl.get().label);
				fire_args.add(e);
				pre = ExprBadJoin.make(null, null, e, pre);
				post = ExprBadJoin.make(null, null, e, post);
				fir = ExprBadJoin.make(null, null, e, fir);
			}

			for (int i = acts_args.get(act_name).size(); i < max_args; i++) 
				fir = ExprBadJoin.make(null, null, dummy_var, fir);
			fir = ExprBadJoin.make(null, null, ExprVar.make(null,actSigName(act_name)), fir);

			fir = fir.implies(pre.and(post));
			
			if (acts_args.get(act_name).size()>0)
				fir = fir.forAll(fire_decls[0], Arrays.copyOfRange(fire_decls, 1, fire_decls.length));

			fir = fir.always();
			final String fire_fact_name = "_fire_"+act_name;
			root.addFact(null, fire_fact_name, fir);

//			System.out.println(act_name+" firing condition: "+ fir);	
		}

		// create the fired predicates (free or fixed args) for each action
		for (String act_name : acts_args.keySet()) {
			List<Decl> decls = new ArrayList<Decl>(acts_args.get(act_name));
//			System.out.print((decls.size()>0?"With":"Without")+" arguments ");
//			for (Decl d : decls) System.out.print(d.names+":"+d.expr+" ");

			Expr v0 = fired_var;
			for (int i = 0; i < max_args; i ++) {
				ExprVar yy = i>=decls.size()?dummy_var:ExprVar.make(null, decls.get(i).get().label);
				v0 = yy.join(v0);
			}
			v0 = ExprVar.make(null, actSigName(act_name)).join(v0);
			if (decls.size()>0) {
				root.addFunc(null, null, curPredName(act_name), null, decls, null, v0);
				root.addFunc(null, null, act_name, null, null, null, v0.forSome(decls.remove(0),decls.toArray(new Decl[decls.size()])));
			} else {
				root.addFunc(null, null, curPredName(act_name), null, null, null, v0);
				root.addFunc(null, null, act_name, null, null, null, v0);
			}
//			System.out.println("defined predicate "+act_name+" with "+v0);
//			System.out.println("defined predicate "+curPredName(act_name)+" with "+v0);
			
		}
		
		// create the frame condition fact
		Expr fc_body = ExprConstant.TRUE;
		// for each occurrence in modified clause, create frame condition
		for (String evv : acts_mods.keySet()) {
			Expr sss = ExprConstant.FALSE;
			for (Sig s : acts_mods.get(evv))
				sss = sss.or(ExprVar.make(null, s.label.substring(6)));
			fc_body = fc_body.and((ExprVar.make(null,evv).equal(ExprUnary.Op.PRIME.make(null, ExprVar.make(null,evv))).not()).implies(sss));
		}
		for (Sig svv : root.getAllSigs()) {
			if (!(acts_mods.keySet().contains(svv.label.substring(5))))
				fc_body = fc_body.and((ExprVar.make(null,svv.label).equal(ExprUnary.Op.PRIME.make(null, ExprVar.make(null,svv.label)))));
			if (old2fields.get(svv) != null)
				for (Decl fvv0 : old2fields.get(svv))
					for (ExprHasName fvv : fvv0.names)
						if (!(acts_mods.keySet().contains(fvv.label)))
							fc_body = fc_body.and((ExprVar.make(null,fvv.label).equal(ExprUnary.Op.PRIME.make(null, ExprVar.make(null,fvv.label)))));
		}
		
		final String fc_name = "_fc";
		fc_body = fc_body.always();
		root.addFact(null, fc_name, fc_body);
//		System.out.println("FC fact "+fc_name+" defined: "+fc_body);
	}
	
	/**
	 * Expands an Action definition into regular Alloy. Only applies expansions
	 * that can be calculated independently from other Actions (i.e., not
	 * dependent on the maximum number of arguments).
	 * 
	 * @param root
	 *            the Alloy module
	 * @param p
	 *            the position of the declaration
	 * @param isPrivate
	 *            whether it is private
	 * @param n
	 *            the name of the action
	 * @param decls
	 *            the parameters
	 * @param body
	 *            the body
	 * @param mods
	 *            the modified elements
	 * @throws Err
	 */
	public void expandAction(CompModule root, Pos p, Pos isPrivate, String n, List<Decl> decls, Expr body, List<ExprVar> mods) throws Err {
		// creates a singleton sig representing th action, extending Action
		List<ExprVar> sig_action = Util.asList(ExprVar.make(null, "_Action"));
		Sig sig_this = root.addSig(actSigName(n), ExprVar.make(null, "extends"), sig_action, null, null, Attr.ONE, Attr.PRIVATE);
//		System.out.println("Created sig "+sig_this.label+" with "+sig_this.attributes+".");

		// stores the arguments of this action (needed generating the succeeding constraints depending on total arguments)
		if (decls == null) decls = new ArrayList<Decl>();
		List<Decl> decls_exp = new ArrayList<Decl>();
		for (Decl d : decls)
			for (ExprHasName nm : d.names)
				decls_exp.add(new Decl(d.isVar, d.isPrivate, d.disjoint, d.disjoint2, Util.asList(nm), d.expr));
		acts_args.put(n, decls_exp);

		// create the pre- and post-condition predicates pre#n[..] and post#n[..] for the splitting of body
		// the arguments are the same as the action
		// the fired predicate cannot be expanded at this stage as it needs the maximum number of arguments
		List<Expr> v1 = new ArrayList<Expr>(), v2 = new ArrayList<Expr>();
        body = (new ConvToConjunction()).visitThis(body);
        recursiveSplit(body, v1, v2);
        v1.add(NONE.no());
        v2.add(NONE.no());
			
        root.addFunc(p, isPrivate, prePredName(n), null, decls, null, ExprList.make(null, null, ExprList.Op.AND, v1));
		root.addFunc(p, isPrivate, postPredName(n), null, decls, null, ExprList.make(null, null, ExprList.Op.AND, v2));
//		System.out.print((decls.size()>0?"With":"Without")+" arguments ");
//		for (Decl d : decls) System.out.print(d.names+":"+d.expr+" ");
//		System.out.println("defined:");
//		System.out.println("predicate "+prePredName(n)+" with "+ExprList.make(null, null, ExprList.Op.AND, v1));
//		System.out.println("predicate "+postPredName(n)+" with "+ExprList.make(null, null, ExprList.Op.AND, v2));
		
		// store modified elements, cannot be expanded at this stage as it the modifies from other actions
		if (mods == null) mods = new ArrayList<ExprVar>();
		for (ExprVar xx : mods) {
			List<Sig> ss = acts_mods.get(xx.label);
			if (ss == null) ss = new ArrayList<Sig>();
			ss.add(sig_this);
			acts_mods.put(xx.label, ss);
		}
	}
	
	static private String actSigName(String n) {
		return "_"+n;
	}

	static private String prePredName(String n) {
		return "pre_"+n;
	}

	static private String postPredName(String n) {
		return "post_"+n;
	}

	static private String curPredName(String n) {
		return "cur_"+n;
	}

	/**
	 * Splits the conjuncts of an expression depending on whether it contains
	 * temporal operators.
	 * 
	 * @param v
	 *            the original expression
	 * @param v1
	 *            the conjuncts without temporal operators
	 * @param v2
	 *            the conjuncts with temporal operators
	 */
	private void recursiveSplit(Expr v, List<Expr> v1, List<Expr> v2) {
        if (v instanceof ExprList && ((ExprList)v).op==ExprList.Op.AND) {
            for(Expr e: ((ExprList)v).args) recursiveSplit(e,v1,v2);
        } else if (v instanceof ExprBinary && ((ExprBinary)v).op==ExprBinary.Op.AND) {
        	recursiveSplit(((ExprBinary) v).left,v1,v2);
        	recursiveSplit(((ExprBinary) v).right,v1,v2);
        }
        else {
			final VisitQuery<Object> q = new VisitQuery<Object>() {
				@Override
				public final Object visit(ExprUnary x) throws Err {
					if (((ExprUnary) x).op == ExprUnary.Op.PRIME
							|| ((ExprUnary) x).op == ExprUnary.Op.AFTER
							|| ((ExprUnary) x).op == ExprUnary.Op.PREVIOUS
							|| ((ExprUnary) x).op == ExprUnary.Op.ALWAYS
							|| ((ExprUnary) x).op == ExprUnary.Op.HISTORICALLY
							|| ((ExprUnary) x).op == ExprUnary.Op.EVENTUALLY
							|| ((ExprUnary) x).op == ExprUnary.Op.ONCE)
						return x;
					else return super.visit(x);
				}
				@Override
				public final Object visit(ExprBinary x) throws Err {
					if (((ExprBinary) x).op == ExprBinary.Op.UNTIL
							|| ((ExprBinary) x).op == ExprBinary.Op.SINCE
							|| ((ExprBinary) x).op == ExprBinary.Op.RELEASE)
						return x;
					else return super.visit(x);
				}
				@Override
			    public final Object visit(ExprBadCall x) throws Err { 
			        for(Expr y:x.args) { Object ans=y.accept(this); if (ans!=null) return ans; }
			        return null;
				}
				@Override
			    public final Object visit(ExprBadJoin x) throws Err { 
			        Object ans=x.left.accept(this);
			        if (ans==null) ans=x.right.accept(this);
			        return ans;
				}
			};
			try {
				Object qr = q.visitThis(v);
				if (qr==null) v1.add(v);
				else  v2.add(v);
			} catch (Err e) {
				e.printStackTrace();
			}
        }
	}

	public String isAct(String l) {
		if (acts_args.get(l) != null)
			return curPredName(l);
		else return null;
	}
}
