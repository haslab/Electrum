/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 * Electrum -- Copyright (c) 2015-present, Nuno Macedo
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

import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.NONE;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.SEQIDX;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.SIGINT;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.STRING;
import static edu.mit.csail.sdg.alloy4compiler.ast.Sig.UNIV;

import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import kodkod.ast.Relation;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4.XMLNode;
import edu.mit.csail.sdg.alloy4compiler.ast.Attr;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.SubsetSig;

/**
 * This helper class contains helper routines for reading an A4Solution object
 * from an XML file.
 * 
 * @modified: Nuno Macedo, Eduardo Pessoa // [HASLab] electrum-temporal
 * */

public final class A4SolutionReader {

	/** The resulting A4Solution object. */
	// [HASLab] removed final, trace solutions
	private A4Solution sol;

	/** The provided choices of existing Sig and Field. */
	private final LinkedHashSet<Expr> choices = new LinkedHashSet<Expr>();

	/** Stores the set of atoms. */
	private final TreeSet<String> atoms = new TreeSet<String>();

	/** Stores the set of STRING atoms. */
	private final TreeSet<String> strings = new TreeSet<String>();

	/** Maps each Sig/Field/Skolem id to an XMLNode. */
	private final Map<String, XMLNode> nmap = new LinkedHashMap<String, XMLNode>();

	/** Maps each Sig id to a Sig. */
	private final Map<String, Sig> id2sig = new LinkedHashMap<String, Sig>();

	/** Stores the set of all sigs. */
	private final Set<Sig> allsigs = Util.asSet((Sig) UNIV, SIGINT, SEQIDX, STRING, NONE);

	/** Mapes each expression we've seen to its TupleSet. */
	private final Map<Expr, TupleSet> expr2ts = new LinkedHashMap<Expr, TupleSet>();

	/** The Kodkod tupleset factory. */
	// [HASLab] removed final, trace solutions
	private TupleFactory factory;

	/**
	 * Helper method that returns true if the given attribute value in the given
	 * XML node is equal to "yes"
	 */
	private static boolean yes(XMLNode node, String attr) {
		return node.getAttribute(attr).equals("yes");
	}

	/** Helper method that returns an XML node's "label" attribute. */
	private static String label(XMLNode node) {
		return node.getAttribute("label");
	}

	/**
	 * Helper method that returns true if the two iterables contain the same
	 * elements (though possibly in different order)
	 */
	private static boolean sameset(Iterable<Sig> a, Iterable<Sig> b) {
		ArrayList<Sig> tmp = new ArrayList<Sig>();
		for (Sig x : b)
			tmp.add(x);
		for (Sig x : a)
			if (tmp.contains(x))
				tmp.remove(x);
			else
				return false;
		return tmp.isEmpty();
	}

	/** Parse tuple. */
	private Tuple parseTuple(XMLNode tuple, int arity) throws Err {
		Tuple ans = null;
		try {
			for (XMLNode sub : tuple)
				if (sub.is("atom")) {
					Tuple x = factory.tuple(sub.getAttribute("label"));
					if (ans == null)
						ans = x;
					else
						ans = ans.product(x);
				}
			if (ans == null)
				throw new ErrorFatal("Expecting: <tuple> <atom label=\"..\"/> .. </tuple>");
			if (ans.arity() != arity)
				throw new ErrorFatal("Expecting: tuple of arity " + arity + " but got tuple of arity " + ans.arity());
			return ans;
		} catch (Throwable ex) {
			throw new ErrorFatal("Expecting: <tuple> <atom label=\"..\"/> .. </tuple>", ex);
		}
	}

	/** Parse tuples. */
	private TupleSet parseTuples(XMLNode tuples, int arity) throws Err {
		TupleSet ans = factory.noneOf(arity);
		for (XMLNode sub : tuples)
			if (sub.is("tuple"))
				ans.add(parseTuple(sub, arity));
		return ans;
	}

	/** Parse sig/set. */
	private Sig parseSig(String id, int depth) throws IOException, Err {
		Sig ans = id2sig.get(id);
		// [HASLab] if created in previous steps of the trace re-use sig but must still calculate current atoms
		// if (ans != null)
		// 	return ans;
		XMLNode node = nmap.get(id);
		if (node == null)
			throw new IOException("Unknown SigID " + id + " encountered.");
		if (!node.is("sig"))
			throw new IOException("ID " + id + " is not a sig.");
		String label = label(node);
		Attr isAbstract = yes(node, "abstract") ? Attr.ABSTRACT : null;
		Attr isOne = yes(node, "one") ? Attr.ONE : null;
		Attr isLone = yes(node, "lone") ? Attr.LONE : null;
		Attr isSome = yes(node, "some") ? Attr.SOME : null;
		Attr isPrivate = yes(node, "private") ? Attr.PRIVATE : null;
		Attr isMeta = yes(node, "meta") ? Attr.META : null;
		Attr isEnum = yes(node, "enum") ? Attr.ENUM : null;
		Attr isExact = yes(node, "exact") ? Attr.EXACT : null;
		Attr isVar = yes(node, "var") ? Attr.VARIABLE : null; // [HASLab]
		if (yes(node, "builtin")) {
			if (label.equals(UNIV.label)) {
				id2sig.put(id, UNIV);
				return UNIV;
			}
			if (label.equals(SIGINT.label)) {
				id2sig.put(id, SIGINT);
				return SIGINT;
			}
			if (label.equals(SEQIDX.label)) {
				id2sig.put(id, SEQIDX);
				return SEQIDX;
			}
			if (label.equals(STRING.label)) {
				id2sig.put(id, STRING);
				return STRING;
			}
			throw new IOException("Unknown builtin sig: " + label + " (id=" + id + ")");
		}
		if (depth > nmap.size())
			throw new IOException("Sig " + label + " (id=" + id + ") is in a cyclic inheritance relationship.");
		List<Sig> parents = null;
		TupleSet ts = factory.noneOf(1);
		for (XMLNode sub : node) {
			if (sub.is("atom")) {
				ts.add(factory.tuple(sub.getAttribute("label")));
				continue;
			}
			if (!sub.is("type"))
				continue;
			Sig parent = parseSig(sub.getAttribute("ID"), depth + 1);
			if (parents == null)
				parents = new ArrayList<Sig>();
			parents.add(parent);
		}
		if (parents == null) {
			String parentID = node.getAttribute("parentID");
			Sig parent = parseSig(parentID, depth + 1);
			if (!(parent instanceof PrimSig))
				throw new IOException("Parent of sig " + label + " (id=" + id + ") must not be a subset sig.");
			for (Expr choice : choices)
				if (choice instanceof PrimSig && parent == ((PrimSig) choice).parent
						&& ((Sig) choice).label.equals(label)) {
					ans = (Sig) choice;
					choices.remove(choice);
					break;
				}
			if (ans == null) {
				ans = new PrimSig(label, (PrimSig) parent, isAbstract, isLone, isOne, isSome, isPrivate, isMeta, isEnum, isVar); // [HASLab]
				allsigs.add(ans);
			}
		} else {
			for (Expr choice : choices)
				if (choice instanceof SubsetSig && ((Sig) choice).label.equals(label)
						&& sameset(parents, ((SubsetSig) choice).parents)) {
					ans = (Sig) choice;
					choices.remove(choice);
					break;
				} else if (choice instanceof PrimSig && ((Sig) choice).label.equals(label)  // [HASLab] variable sigs are subsigs except when top
						&& parents.size() == 1
						&& parents.get(0).equals(((PrimSig) choice).parent)) {
					ans = (Sig) choice;
					choices.remove(choice);
					break;
				}
			if (ans == null) {
				if (isVar != null && parents.get(0) == UNIV) // [HASLab] variable sigs are subsigs except when top
					ans = new PrimSig(label, (PrimSig) parents.get(0), isAbstract, isLone, isOne, isSome, isPrivate, isMeta, isEnum, isVar); // [HASLab]
				else
					ans = new SubsetSig(label, parents, isExact, isLone, isOne, isSome, isPrivate, isMeta, isVar); // [HASLab]
				allsigs.add(ans);
			}
		}
		id2sig.put(id, ans);
		expr2ts.put(ans, ts);
		if (ans instanceof PrimSig)
			// Add the atoms in this SIG into all parent sigs
			for (PrimSig ans2 = ((PrimSig) ans).parent; ans2 != null && !ans2.builtin; ans2 = ans2.parent) {
				TupleSet ts2 = expr2ts.get(ans2);
				if (ts2 == null)
					ts2 = ts.clone();
				else {
					ts2 = ts2.clone();
					ts2.addAll(ts);
				}
				expr2ts.put(ans2, ts2);
			}
		else if (ans instanceof SubsetSig && ans.isVariable != null && parents == null) { // [HASLab] variable sigs are subsigs except when top
			// Add the atoms in this SIG into all parent sigs
			for (Sig ans2 = ((SubsetSig) ans).parents.get(0); ans2 != null && !ans2.builtin; ans2 = (ans2 instanceof PrimSig) ? ((PrimSig)ans2).parent:((SubsetSig)ans2).parents.get(0)) {
				TupleSet ts2 = expr2ts.get(ans2);
				if (ts2 == null)
					ts2 = ts.clone();
				else {
					ts2 = ts2.clone();
					ts2.addAll(ts);
				}
				expr2ts.put(ans2, ts2);
			}
		}
		return ans;
	}

	/** Parse type. */
	private Expr parseType(XMLNode node) throws IOException, Err {
		Expr expr = null;
		if (!node.is("types"))
			throw new IOException("<types>...</type> expected");
		for (XMLNode n : node)
			if (n.is("type")) {
				Sig sig = parseSig(n.getAttribute("ID"), 0);
				if (expr == null)
					expr = sig;
				else
					expr = expr.product(sig);
			}
		if (expr == null)
			throw new IOException("<type ID=../> expected");
		return expr;
	}

	/** Parse field. */
	private Field parseField(String id) throws IOException, Err {
		final XMLNode node = nmap.get(id);
		if (node == null)
			throw new IOException("Unknown FieldID " + id + " encountered.");
		if (!node.is("field"))
			throw new IOException("ID " + id + " is not a field.");
		String label = label(node);
		Pos isPrivate = yes(node, "private") ? Pos.UNKNOWN : null;
		Pos isMeta = yes(node, "meta") ? Pos.UNKNOWN : null;
		Pos isVar = yes(node, "var") ? Pos.UNKNOWN : null; // [HASLab]
		Expr type = null;
		for (XMLNode sub : node)
			if (sub.is("types")) {
				Expr t = parseType(sub);
				if (type == null)
					type = t;
				else
					type = type.plus(t);
			}
		int arity;
		if (type == null || (arity = type.type().arity()) < 2)
			throw new IOException("Field " + label + " is maltyped.");
		String parentID = node.getAttribute("parentID");
		Sig parent = id2sig.get(parentID);
		if (parent == null)
			throw new IOException("ID " + parentID + " is not a sig.");
		Field field = null;
		for (Field f : parent.getFields())
			if (f.label.equals(label) && f.type().arity() == arity && choices.contains(f)) {
				field = f;
				choices.remove(f);
				break;
			}
		if (field == null)
			field = parent.addTrickyField(Pos.UNKNOWN, isPrivate, null, null, isMeta, isVar, new String[] { label }, // [HASLab]
					UNIV.join(type))[0];
		TupleSet ts = parseTuples(node, arity);
		expr2ts.put(field, ts);
		return field;
	}

	/** Parse skolem. */
	private ExprVar parseSkolem(String id) throws IOException, Err {
		final XMLNode node = nmap.get(id);
		if (node == null)
			throw new IOException("Unknown ID " + id + " encountered.");
		if (!node.is("skolem"))
			throw new IOException("ID " + id + " is not a skolem.");
		String label = label(node);
		Expr type = null;
		for (XMLNode sub : node)
			if (sub.is("types")) {
				Expr t = parseType(sub);
				if (type == null)
					type = t;
				else
					type = type.plus(t);
			}
		int arity;
		if (type == null || (arity = type.type().arity()) < 1)
			throw new IOException("Skolem " + label + " is maltyped.");
		// [HASLab] try to use previously created expr for skolem, not mapped anywhere
		ExprVar var = null;
		for (Expr exp : expr2ts.keySet())
			if (exp instanceof ExprVar && ((ExprVar) exp).label.equals(label))
				var = (ExprVar) exp;
		if (var == null)
			var = ExprVar.make(Pos.UNKNOWN, label, type.type());
		TupleSet ts = parseTuples(node, arity);
		expr2ts.put(var, ts);
		return var;
	}

	/** Parse everything. */
	// [HASLab] modified to support sequences of <instance> nodes
	private A4SolutionReader(Iterable<Sig> sigs, XMLNode xml) throws IOException, Err {
		// find <instance>..</instance>
		if (!xml.is("alloy"))
			throw new ErrorSyntax("The XML file's root node must be <alloy> or <instance>.");
		XMLNode inst = null;
		A4Solution prev = null;
		for (XMLNode sub : xml)
			if (sub.is("instance")) {
				inst = sub;
				break;
			}
				
		if (inst == null)
			throw new ErrorSyntax("The XML file must contain an <instance> element.");

		// set up the basic values of the A4Solution object
		final int bitwidth = Integer.parseInt(inst.getAttribute("bitwidth"));
		final int maxseq = Integer.parseInt(inst.getAttribute("maxseq"));
		final int tracelength = Integer.parseInt(inst.getAttribute("tracelength"));  // [HASLab]
		final int backloop = Integer.parseInt(inst.getAttribute("backloop")); 		 // [HASLab]
		final int max = Util.max(bitwidth), min = Util.min(bitwidth);
		if (bitwidth >= 1 && bitwidth <= 30)
			for (int i = min; i <= max; i++) {
				atoms.add(Integer.toString(i));
			}
		
		// [HASLab] get all atoms of the universe, must traverse all steps
		for (XMLNode sub : xml)
			if (sub.is("instance")) {
				inst = sub;
				for (XMLNode x : inst) {
					if (x.is("sig")) {
						boolean isString = STRING.label.equals(label(x)) && yes(x, "builtin");
						for (XMLNode y : x)
							if (y.is("atom")) {
								String attr = y.getAttribute("label");
								atoms.add(attr);
								if (isString)
									strings.add(attr);
							}
					}
				}
			}

		int st = -1;
		for (XMLNode sub : xml) 
			if (sub.is("instance")) {
				inst = sub;
				st++;
				
				// [HASLab] if not first step, retrieve already created sigs
				prev = sol;
				if (prev != null)
					sigs = prev.getAllReachableSigs();

				for (Sig s : sigs)
					if (!s.builtin) {
						allsigs.add(s);
						choices.add(s);
						for (Field f : s.getFields())
							choices.add(f);
					}
				
				nmap.clear();
				for (XMLNode x : inst) {
					String id = x.getAttribute("ID");
					if (id.length() > 0 && (x.is("field") || x.is("skolem") || x.is("sig"))) {
						if (nmap.put(id, x) != null)
							throw new IOException("ID " + id + " is repeated.");
					}
				}
				
				// create the A4Solution object
				A4Options opt = new A4Options();
				opt.originalFilename = inst.getAttribute("filename");
				sol = new A4Solution(inst.getAttribute("command"), bitwidth, tracelength, tracelength, maxseq, strings, atoms, null, opt, 1); // [HASLab]
				factory = sol.getFactory();
				// [HASLab] only set backloop if that state already processed
				if (backloop <= st)
					sol.setBackLoop(backloop); 
				// parse all the sigs, fields, and skolems
				for (Map.Entry<String, XMLNode> e : nmap.entrySet())
					if (e.getValue().is("sig"))
						parseSig(e.getKey(), 0);
				for (Map.Entry<String, XMLNode> e : nmap.entrySet())
					if (e.getValue().is("field"))
						parseField(e.getKey());
				for (Map.Entry<String, XMLNode> e : nmap.entrySet())
					if (e.getValue().is("skolem"))
						parseSkolem(e.getKey());
				for (Sig s : allsigs)
					if (!s.builtin) {
						TupleSet ts = expr2ts.remove(s);
						if (ts == null)
							ts = factory.noneOf(1); // If the sig was NOT mentioned in the XML file...
						Relation r;
						// [HASLab] if first set create the relation
						if (prev == null) 
							r = sol.addRel(s.label, ts, ts, s.isVariable!=null);
						// [HASLab] otherwise use previously created
						else {
							r = (Relation) prev.a2k(s);
							sol.addPreRel(s.label, ts, ts, r);
						}
						sol.addSig(s, r);
						for (Field f : s.getFields()) {
							ts = expr2ts.remove(f);
							if (ts == null)
								ts = factory.noneOf(f.type().arity()); // If the field was NOT mentioned in the XML file...
							// [HASLab] if first set create the relation
							if (prev == null)
								r = sol.addRel(s.label + "." + f.label, ts, ts, f.isVariable!=null);
							// [HASLab] otherwise use previously created
							else {
								r = (Relation) prev.a2k(f);
								sol.addPreRel(s.label + "." + f.label, ts, ts, r);
							}
							sol.addField(f, r);
						}
					}
				for (Map.Entry<Expr, TupleSet> e : expr2ts.entrySet()) {
					ExprVar v = (ExprVar) (e.getKey());
					TupleSet ts = e.getValue();
					Relation r = null;
					if (prev == null) r = sol.addRel(v.label, ts, ts, true);
					else {
						// [HASLab] try to use previously created relation for skolem, not mapped anywhere
						for (Expr exp : prev.a2k().keySet())
							if (exp instanceof ExprVar && ((Relation) prev.a2k(exp)).name().equals(v.label)) {
								r = (Relation) prev.a2k(exp); break;
							}
						sol.addPreRel(v.label, ts, ts, r);
					}
					sol.kr2type(r, v.type());
				}
				// Done!
				sol.solve(null, prev); // [HASLab] merge current solution with previous, if any
			}
	}

	/**
	 * Parse the XML element into an AlloyInstance.
	 *
	 * <p>
	 * The list of sigs, if not null, will be used as the sigs (and their
	 * fields) that we expect to exist; <br>
	 * if there's a sig or field X in the list but not in the XML, then X's
	 * tupleset will be regarded as empty; <br>
	 * if there's a sig or field X in the XML but not in the list, then X (and
	 * its value in XML file) is added to the solution.
	 */
	public static A4Solution read(Iterable<Sig> sigs, XMLNode xml) throws Err {
		try {
			if (sigs == null)
				sigs = new ArrayList<Sig>();
			A4SolutionReader x = new A4SolutionReader(sigs, xml);
			return x.sol;
		} catch (Throwable ex) {
			if (ex instanceof Err)
				throw ((Err) ex);
			else
				throw new ErrorFatal("Fatal error occured: " + ex, ex);
		}
	}
}
