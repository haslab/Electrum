/* Alloy Analyzer 4 -- Copyright (c) 2006-2009, Felix Chang
 * Electrum -- Copyright (c) 2014-present, Nuno Macedo
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
import static kodkod.engine.Solution.Outcome.UNSATISFIABLE;

import java.io.File;
import java.io.IOException;
import java.io.PrintWriter;
import java.text.DateFormat;
import java.text.SimpleDateFormat;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Date;
import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import kodkod.ast.BinaryExpression;
import kodkod.ast.BinaryFormula;
import kodkod.ast.Decl;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.IntExpression;
import kodkod.ast.Node;
import kodkod.ast.Relation;
import kodkod.ast.VarRelation;
import kodkod.ast.Variable;
import kodkod.ast.operator.ExprOperator;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.CapacityExceededException;
import kodkod.engine.Evaluator;
import kodkod.engine.PardinusSolver;
import kodkod.engine.Proof;
import kodkod.engine.Solution;
import kodkod.engine.config.ExtendedOptions;
import kodkod.engine.config.Options;
import kodkod.engine.config.Reporter;
import kodkod.engine.config.SLF4JReporter;
import kodkod.engine.fol2sat.TranslationRecord;
import kodkod.engine.fol2sat.Translator;
import kodkod.engine.satlab.SATFactory;
import kodkod.engine.ucore.HybridStrategy;
import kodkod.engine.ucore.RCEStrategy;
import kodkod.instance.Bounds;
import kodkod.instance.Instance;
import kodkod.instance.PardinusBounds;
import kodkod.instance.TemporalInstance;
import kodkod.instance.Tuple;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;
import kodkod.util.ints.IndexedEntry;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.ConstList;
import edu.mit.csail.sdg.alloy4.ConstMap;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorAPI;
import edu.mit.csail.sdg.alloy4.ErrorFatal;
import edu.mit.csail.sdg.alloy4.ErrorSyntax;
import edu.mit.csail.sdg.alloy4.Pair;
import edu.mit.csail.sdg.alloy4.Pos;
import edu.mit.csail.sdg.alloy4.SafeList;
import edu.mit.csail.sdg.alloy4.UniqueNameGenerator;
import edu.mit.csail.sdg.alloy4.Util;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprBinary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprConstant;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprUnary;
import edu.mit.csail.sdg.alloy4compiler.ast.ExprVar;
import edu.mit.csail.sdg.alloy4compiler.ast.Func;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.Field;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.ast.Type;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options.SatSolver;

/** This class stores a SATISFIABLE or UNSATISFIABLE solution.
 * It is also used as a staging area for the solver before generating the solution.
 * Once solve() has been called, then this object becomes immutable after that.
 * 
 * @modified: Nuno Macedo, Eduardo Pessoa // [HASLab] temporal solving
 */

public final class A4Solution {

	//====== static immutable fields ====================================================================//

	/** The constant unary relation representing the smallest Int atom. */
	static final Relation KK_MIN = Relation.unary("Int/min");

	/** The constant unary relation representing the Int atom "0". */
	static final Relation KK_ZERO = Relation.unary("Int/zero");

	/** The constant unary relation representing the largest Int atom. */
	static final Relation KK_MAX = Relation.unary("Int/max");

	/** The constant binary relation representing the "next" relation from each Int atom to its successor. */
	static final Relation KK_NEXT = Relation.binary("Int/next");

	/** The constant unary relation representing the set of all seq/Int atoms. */
	static final Relation KK_SEQIDX = Relation.unary("seq/Int");

	/** The constant unary relation representing the set of all String atoms. */
	static final Relation KK_STRING = Relation.unary("String");

	//====== immutable fields ===========================================================================//

	/** The original Alloy options that generated this solution. */
	private final A4Options originalOptions;

	/** The original Alloy command that generated this solution; can be "" if unknown. */
	private final String originalCommand;

	/** The bitwidth; always between 1 and 30. */
	private final int bitwidth;

	/** The maximum allowed sequence length; always between 0 and 2^(bitwidth-1)-1. */
	private final int maxseq;

	/** The maximum allowed number of loop unrolling and recursion level. */
	private final int unrolls;

	/** The list of all atoms. */
	private final ConstList<String> kAtoms;

	/** The Kodkod TupleFactory object. */
	private final TupleFactory factory;

	/** The set of all Int atoms; immutable. */
	private final TupleSet sigintBounds;

	/** The set of all seq/Int atoms; immutable. */
	private final TupleSet seqidxBounds;

	/** The set of all String atoms; immutable. */
	private final TupleSet stringBounds;

	/** The Temporal Kodkod Solver object. */
	// [HASLab]
	private final PardinusSolver solver;

	//====== mutable fields (immutable after solve() has been called) ===================================//

	/** True iff the problem is solved. */
	private boolean solved = false;

	/** The Kodkod Temporal Bounds object. */
	// [HASLab]
	private PardinusBounds bounds; 

	/** The list of Kodkod formulas; can be empty if unknown; once a solution is solved we must not modify this anymore */
	private ArrayList<Formula> formulas = new ArrayList<Formula>();

	/** The list of known Alloy4 sigs. */
	private SafeList<Sig> sigs;

	/** If solved==true and is satisfiable, then this is the list of known skolems. */
	private SafeList<ExprVar> skolems = new SafeList<ExprVar>();

	/** If solved==true and is satisfiable, then this is the list of actually used atoms. */
	private SafeList<ExprVar> atoms = new SafeList<ExprVar>();
	
	/** If solved==true and is satisfiable, then this maps each Kodkod atom to a short name. */
	private Map<Object,String> atom2name = new LinkedHashMap<Object,String>();

	/** If solved==true and is satisfiable, then this maps each Kodkod atom to its most specific sig. */
	private Map<Object,PrimSig> atom2sig = new LinkedHashMap<Object,PrimSig>();

	/** If solved==true and is satisfiable, then this is the Kodkod evaluator. */
	private Evaluator eval = null;

	/** If not null, you can ask it to get another solution. */
	private Iterator<Solution> kEnumerator = null; 

	/** The map from each Sig/Field/Skolem/Atom to its corresponding Kodkod expression. */
	private Map<Expr,Expression> a2k;

	/** The map from each String literal to its corresponding Kodkod expression. */
	private final ConstMap<String,Expression> s2k;

	/** The map from each kodkod Formula to Alloy Expr or Alloy Pos (can be empty if unknown) */
	private Map<Formula,Object> k2pos;

	/** The map from each Kodkod Relation to Alloy Type (can be empty or incomplete if unknown) */
	private Map<Relation,Type> rel2type;

	/** The map from each Kodkod Variable to an Alloy Type and Alloy Pos. */
	private Map<Variable,Pair<Type,Pos>> decl2type;

	/** The maximum trace length of this solution. */
	// [HASLab]
	private int traceLength;
	
	/** The back loop instant of this solution, if any (-1 otherwise). */
	// [HASLab]
	private int backLoop;

	//===================================================================================================//
	
	/** Construct a blank A4Solution containing just UNIV, SIGINT, SEQIDX, STRING, and NONE as its only known sigs.
	 * @param originalCommand  - the original Alloy command that generated this solution; can be "" if unknown
	 * @param bitwidth - the bitwidth; must be between 1 and 30
	 * @param maxseq - the maximum allowed sequence length; must be between 0 and (2^(bitwidth-1))-1
	 * @param atoms - the set of atoms
	 * @param rep - the reporter that will receive diagnostic and progress messages
	 * @param opt - the Alloy options that will affect the solution and the solver
	 * @param expected - whether the user expected an instance or not (1 means yes, 0 means no, -1 means the user did not express an expectation)
	 */ 
	 // [HASLab] adapted to consider temporal problems, solutions and options.
	A4Solution(String originalCommand, int bitwidth, int minTracelength, int maxTracelength, int maxseq, Set<String> stringAtoms, Collection<String> atoms, final A4Reporter rep, A4Options opt, int expected) throws Err {
		opt = opt.dup();
		this.canAddSkolems = true; // [HASLab] pessoa: in the first renaming the atoms are added
		this.temporalAtoms = new GatherTemporalAtoms(); // [HASLab] pessoa: the object is initialized to gather all atoms in the renaming procedure
		this.unrolls = opt.unrolls;
		this.sigs = new SafeList<Sig>(Arrays.asList(UNIV, SIGINT, SEQIDX, STRING, NONE));
		this.a2k = Util.asMap(new Expr[]{UNIV, SIGINT, SEQIDX, STRING, NONE}, Relation.INTS.union(KK_STRING), Relation.INTS, KK_SEQIDX, KK_STRING, Relation.NONE);
		this.k2pos = new LinkedHashMap<Formula,Object>();
		this.rel2type = new LinkedHashMap<Relation,Type>();
		this.decl2type = new LinkedHashMap<Variable,Pair<Type,Pos>>();
		this.originalOptions = opt;
		this.originalCommand = (originalCommand==null ? "" : originalCommand);
		this.bitwidth = bitwidth;
		this.traceLength = maxTracelength; // [HASLab]
		this.maxseq = maxseq;
		if (bitwidth < 0)   throw new ErrorSyntax("Cannot specify a bitwidth less than 0");
		if (bitwidth > 30)  throw new ErrorSyntax("Cannot specify a bitwidth greater than 30");
		if (maxseq < 0)     throw new ErrorSyntax("The maximum sequence length cannot be negative.");
		if (maxseq > 0 && maxseq > max()) throw new ErrorSyntax("With integer bitwidth of "+bitwidth+", you cannot have sequence length longer than "+max());
		if (atoms.isEmpty()) {
			atoms = new ArrayList<String>(1);
			atoms.add("<empty>");
		}
		kAtoms = ConstList.make(atoms);
		bounds = new PardinusBounds(new Universe(kAtoms)); // [HASLab] temporal bounds
		factory = bounds.universe().factory();
		TupleSet sigintBounds = factory.noneOf(1);
		TupleSet seqidxBounds = factory.noneOf(1);
		TupleSet stringBounds = factory.noneOf(1);
		final TupleSet next = factory.noneOf(2);
		int min=min(), max=max();
		if (max >= min) for(int i=min; i<=max; i++) { // Safe since we know 1 <= bitwidth <= 30
			Tuple ii = factory.tuple(""+i);
			TupleSet is = factory.range(ii, ii);
			bounds.boundExactly(i, is);
			sigintBounds.add(ii);
			if (i>=0 && i<maxseq) seqidxBounds.add(ii);
			if (i+1<=max) next.add(factory.tuple(""+i, ""+(i+1)));
			if (i==min) bounds.boundExactly(KK_MIN,  is);
			if (i==max) bounds.boundExactly(KK_MAX,  is);
			if (i==0)   bounds.boundExactly(KK_ZERO, is);
		}
		this.sigintBounds = sigintBounds.unmodifiableView();
		this.seqidxBounds = seqidxBounds.unmodifiableView();
		bounds.boundExactly(KK_NEXT, next);
		bounds.boundExactly(KK_SEQIDX, this.seqidxBounds);
		Map<String,Expression> s2k = new HashMap<String,Expression>();
		for(String e: stringAtoms) {
			Relation r = Relation.unary("");
			Tuple t = factory.tuple(e);
			s2k.put(e, r);
			bounds.boundExactly(r, factory.range(t, t));
			stringBounds.add(t);
		}
		this.s2k = ConstMap.make(s2k);
		this.stringBounds = stringBounds.unmodifiableView();
		bounds.boundExactly(KK_STRING, this.stringBounds);
		int sym = (expected==1 ? 0 : opt.symmetry);

		ExtendedOptions varOptions = new ExtendedOptions(); // [HASLab] extended options
		varOptions.setRunTemporal(true); // [HASLab] extended options
		varOptions.setNoOverflow(opt.noOverflow);
		varOptions.setMaxTraceLength(maxTracelength); // [HASLab] propagate options
		varOptions.setMinTraceLength(minTracelength); // [HASLab] propagate options
		varOptions.setRunDecomposed(opt.decomposed); // [HASLab] propagate options
//		solver.options().setFlatten(false); // added for now, since multiplication and division circuit takes forever to flatten // [HASLab] kodkod 2.0+
		// [HASLab] pushed solver creation further below as solver choice is needed for initialization
		if (opt.solver.external()!=null) {
			String ext = opt.solver.external();
			if (opt.solverDirectory.length()>0 && ext.indexOf(File.separatorChar)<0) ext=opt.solverDirectory+File.separatorChar+ext;
			try {
				File tmp = File.createTempFile("tmp", ".cnf", new File(opt.tempDirectory));
				tmp.deleteOnExit(); 
//				solver.options().setSolver(SATFactory.externalFactory(ext, tmp.getAbsolutePath(), "", opt.solver.options())); // [HASLab] kodkod 2.0+
				varOptions.setSolver(SATFactory.externalFactory(ext, tmp.getAbsolutePath(), opt.solver.options()));
			} catch(IOException ex) { throw new ErrorFatal("Cannot create temporary directory.", ex); }
		} else if (opt.solver.equals(A4Options.SatSolver.ZChaffJNI)) { // [HASLab] kodkod 2.0+
//			solver.options().setSolver(SATFactory.ZChaff);
			throw new UnsupportedOperationException("Kodkod no longer supports ZChaff.");
		} else if (opt.solver.equals(A4Options.SatSolver.MiniSatJNI)) {
			varOptions.setSolver(SATFactory.MiniSat);
		} else if (opt.solver.equals(A4Options.SatSolver.MiniSatProverJNI)) {
			sym=20;
			varOptions.setSolver(SATFactory.MiniSatProver);
			varOptions.setLogTranslation(2);
			varOptions.setCoreGranularity(opt.coreGranularity);
		} else if (opt.solver.equals(A4Options.SatSolver.ElectrodS)) { // [HASLab]
			varOptions.setSolver(SATFactory.electrodS());
			varOptions.setRunUnbounded(true);
		} else if (opt.solver.equals(A4Options.SatSolver.ElectrodX)) { // [HASLab]
			varOptions.setSolver(SATFactory.electrodX());
			varOptions.setRunUnbounded(true);
		} else {
			varOptions.setSolver(SATFactory.DefaultSAT4J); // Even for "KK" and "CNF", we choose SAT4J here; later, just before solving, we'll change it to a Write2CNF solver
		}
		varOptions.setSymmetryBreaking(sym);
		varOptions.setSkolemDepth(opt.skolemDepth);
		varOptions.setBitwidth(bitwidth > 0 ? bitwidth : (int) Math.ceil(Math.log(atoms.size())) + 1);
		varOptions.setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
		// [HASLab] create unique readable name
		DateFormat dateFormat = new SimpleDateFormat("yyyy-MM-dd-HH-mm");
		String[] pths = getOriginalFilename().split("/");
		String file = pths[pths.length-1].substring(0, pths[pths.length-1].length()-4).replace(' ', '_');
		String check = getOriginalCommand().replace(' ', '_').replace('$', '-');
		varOptions.setUniqueName(file+"-"+check+"-"+dateFormat.format(new Date())+"-"+this.hashCode());
		solver = new PardinusSolver(varOptions); // [HASLab] temporal solver
	}

	/** Construct a new A4Solution that is the continuation of the old one, but with the "next" instance. */
	 // [HASLab] adapted to consider temporal problems, solutions and options.
	private A4Solution(A4Solution old) throws Err {
		if (!old.solved) throw new ErrorAPI("This solution is not yet solved, so next() is not allowed.");
		if (old.kEnumerator==null) throw new ErrorAPI("This solution was not generated by an incremental SAT solver.\n" + "Solution enumeration is currently only implemented for MiniSat and SAT4J.");
		if (old.eval==null) throw new ErrorAPI("This solution is already unsatisfiable, so you cannot call next() to get the next solution.");
		TemporalInstance inst = (TemporalInstance) old.kEnumerator.next().instance();
		unrolls = old.unrolls;
		originalOptions = old.originalOptions;
		originalCommand = old.originalCommand;
		bitwidth = old.bitwidth;
		backLoop = old.backLoop; // [HASLab] temporal meta-data
		traceLength = old.traceLength; // [HASLab] temporal meta-data
		maxseq = old.maxseq;
		kAtoms = old.kAtoms;
		factory = old.factory;
		sigintBounds = old.sigintBounds;
		seqidxBounds = old.seqidxBounds;
		stringBounds = old.stringBounds;
		solver = old.solver;
		bounds = old.bounds;
		formulas = old.formulas;
		sigs = old.sigs;
		kEnumerator = old.kEnumerator;
		k2pos = old.k2pos;
		rel2type = old.rel2type;
		decl2type = old.decl2type;
		if (inst!=null) {
			traceLength = inst.end; // [HASLab] temporal meta-data
			backLoop = inst.loop; // [HASLab] temporal meta-data
			this.instance = inst; // [HASLab] pessoa: the original instance is kept to perform the renaming
			eval = new Evaluator(inst, old.solver.options());
			a2k = new LinkedHashMap<Expr,Expression>();
			for(Map.Entry<Expr,Expression> e: old.a2k.entrySet())
				if (e.getKey() instanceof Sig || e.getKey() instanceof Field)
					a2k.put(e.getKey(), e.getValue());
			UniqueNameGenerator un = new UniqueNameGenerator();
			rename(this, null, null, un);
			a2k = ConstMap.make(a2k);
		} else {
			skolems = old.skolems;
			eval = null;
			a2k = old.a2k;
		}
		s2k = old.s2k;
		atoms = atoms.dup();
		atom2name = ConstMap.make(atom2name);
		atom2sig = ConstMap.make(atom2sig);
		solved = true;
		temporalAtoms = new GatherTemporalAtoms(); // [HASLab] pessoa
		canAddSkolems = true; // [HASLab] pessoa
	}

	/** Turn the solved flag to be true, and make all remaining fields immutable. */
	private void solved() {
		if (solved) return; // already solved
		bounds = bounds.clone().unmodifiableView();
		sigs = sigs.dup();
		skolems = skolems.dup();
		atoms = atoms.dup();
		atom2name = ConstMap.make(atom2name);
		atom2sig = ConstMap.make(atom2sig);
		a2k = ConstMap.make(a2k);
		k2pos = ConstMap.make(k2pos);
		rel2type = ConstMap.make(rel2type);
		decl2type = ConstMap.make(decl2type);
		solved = true;
	}

	//===================================================================================================//

	/** Returns the bitwidth; always between 1 and 30. */
	public int getBitwidth() { return bitwidth; }

	/** Returns the maximum allowed sequence length; always between 0 and 2^(bitwidth-1)-1. */
	public int getMaxSeq() { return maxseq; }

	/** Returns the largest allowed integer, or -1 if no integers are allowed. */
	public int max() { return Util.max(bitwidth); }

	/** Returns the smallest allowed integer, or 0 if no integers are allowed */
	public int min() { return Util.min(bitwidth); }

	/** Returns the maximum number of allowed loop unrolling or recursion level. */
	public int unrolls() { return unrolls; }

	//===================================================================================================//

	/** Returns the original Alloy file name that generated this solution; can be "" if unknown. */
	public String getOriginalFilename() { return originalOptions.originalFilename; }

	/** Returns the original command that generated this solution; can be "" if unknown. */
	public String getOriginalCommand() { return originalCommand; }

	//===================================================================================================//

	/** Returns the Kodkod input used to generate this solution; returns "" if unknown. */
	public String debugExtractKInput() {  // [HASLab] TODO: why?
		// [HASLab] pessoa: solved or not, the kodkod returned is always the original (without "unuseds")
		return TranslateKodkodToJava.convert(Formula.and(formulas), bitwidth, kAtoms, bounds.unmodifiableView(), null);
//		if (solved)
//			return TranslateKodkodToJava.convert(Formula.and(formulas), bitwidth, kAtoms, bounds, atom2name);
//		else
//			return TranslateKodkodToJava.convert(Formula.and(formulas), bitwidth, kAtoms, bounds.unmodifiableView(), null);
	}

	//===================================================================================================//

	/** Returns the Kodkod TupleFactory object. */
	TupleFactory getFactory() { return factory; }

	/** Returns a modifiable copy of the Kodkod Bounds object. */
	Bounds getBounds() { return bounds.clone(); }

	/** Add a new relation with the given label and the given lower and upper bound.
	 * @param label - the label for the new relation; need not be unique
	 * @param lower - the lowerbound; can be null if you want it to be the empty set
	 * @param upper - the upperbound; cannot be null; must contain everything in lowerbound
	 */
	Relation addRel(String label, TupleSet lower, TupleSet upper, Expr expr) throws ErrorFatal {
		if (solved) throw new ErrorFatal("Cannot add a Kodkod relation since solve() has completed.");
		Relation rel;
		if (expr instanceof  Field){
			if (((Field) expr).isVariable != null){rel = VarRelation.nary(label, upper.arity());} // [HASLab]
			else{rel = Relation.nary(label, upper.arity());}
		}  else {
			if (expr instanceof  Sig){
				if (((Sig) expr).isVariable != null){rel = VarRelation.nary(label, upper.arity());} // [HASLab]
				else{rel = Relation.nary(label, upper.arity());}
			}else{
				rel = Relation.nary(label, upper.arity());
			}
		}
		if (lower == upper) {
			bounds.boundExactly(rel, upper);
		} else if (lower == null) {
			bounds.bound(rel, upper);
		} else {
			if (lower.arity() != upper.arity()) throw new ErrorFatal("Relation "+label+" must have same arity for lowerbound and upperbound.");
			bounds.bound(rel, lower, upper);
		}
		return rel;
	}

	/** Add a new sig to this solution and associate it with the given expression (and if s.isTopLevel then add this expression into Sig.UNIV).
	 * <br> The expression must contain only constant Relations or Relations that are already bound in this solution.
	 * <br> (If the sig was already added by a previous call to addSig(), then this call will return immediately without altering what it is associated with)
	 */
	void addSig(Sig s, Expression expr) throws ErrorFatal {
		if (solved) throw new ErrorFatal("Cannot add an additional sig since solve() has completed.");
		if (expr.arity()!=1) throw new ErrorFatal("Sig "+s+" must be associated with a unary relational value.");
		if (a2k.containsKey(s)) return;
		a2k.put(s, expr);
		sigs.add(s);
		if (s.isTopLevel()) a2k.put(UNIV, a2k.get(UNIV).union(expr));
	}

	/** Add a new field to this solution and associate it with the given expression.
	 * <br> The expression must contain only constant Relations or Relations that are already bound in this solution.
	 * <br> (If the field was already added by a previous call to addField(), then this call will return immediately without altering what it is associated with)
	 */
	void addField(Field f, Expression expr) throws ErrorFatal {
		if (solved) throw new ErrorFatal("Cannot add an additional field since solve() has completed.");
		if (expr.arity()!=f.type().arity()) throw new ErrorFatal("Field "+f+" must be associated with an "+f.type().arity()+"-ary relational value.");
		if (a2k.containsKey(f)) return;
		a2k.put(f, expr);
	}

	/** Add a new skolem to this solution and associate it with the given expression.
	 * <br> The expression must contain only constant Relations or Relations that are already bound in this solution.
	 */
	private ExprVar addSkolem(String label, Type type, Expression expr) throws Err {
		if (solved) throw new ErrorFatal("Cannot add an additional skolem since solve() has completed.");
		int a = type.arity();
		if (a<1) throw new ErrorFatal("Skolem "+label+" must be associated with a relational value.");
		if (a!=expr.arity()) throw new ErrorFatal("Skolem "+label+" must be associated with an "+a+"-ary relational value.");
		ExprVar v = ExprVar.make(Pos.UNKNOWN, label, type);
		a2k.put(v, expr);
		skolems.add(v);
		return v;
	}

	/** Returns an unmodifiable copy of the map from each Sig/Field/Skolem/Atom to its corresponding Kodkod expression. */
	ConstMap<Expr,Expression> a2k()  { return ConstMap.make(a2k); }

	/** Returns an unmodifiable copy of the map from each String literal to its corresponding Kodkod expression. */
	ConstMap<String,Expression> s2k()  { return s2k; }

	/** Returns the corresponding Kodkod expression for the given Sig, or null if it is not associated with anything. */
	Expression a2k(Sig sig)  { return a2k.get(sig); }

	/** Returns the corresponding Kodkod expression for the given Field, or null if it is not associated with anything. */
	Expression a2k(Field field)  { return a2k.get(field); }

	/** Returns the corresponding Kodkod expression for the given Atom/Skolem, or null if it is not associated with anything. */
	Expression a2k(ExprVar var)  { return a2k.get(var); }

	/** Returns the corresponding Kodkod expression for the given String constant, or null if it is not associated with anything. */
	Expression a2k(String stringConstant)  { return s2k.get(stringConstant); }

	/** Returns the corresponding Kodkod expression for the given expression, or null if it is not associated with anything. */
	Expression a2k(Expr expr) throws ErrorFatal {
		while(expr instanceof ExprUnary) {
			if (((ExprUnary)expr).op==ExprUnary.Op.NOOP) { expr = ((ExprUnary)expr).sub; continue; }
			if (((ExprUnary)expr).op==ExprUnary.Op.EXACTLYOF) { expr = ((ExprUnary)expr).sub; continue; }
			break;
		}
		if (expr instanceof ExprConstant && ((ExprConstant)expr).op==ExprConstant.Op.EMPTYNESS) return Expression.NONE;
		if (expr instanceof ExprConstant && ((ExprConstant)expr).op==ExprConstant.Op.STRING) return s2k.get(((ExprConstant)expr).string);
		if (expr instanceof Sig || expr instanceof Field || expr instanceof ExprVar) return a2k.get(expr);
		if (expr instanceof ExprBinary) {
			Expr a=((ExprBinary)expr).left, b=((ExprBinary)expr).right;
			switch(((ExprBinary)expr).op) {
			case ARROW: return a2k(a).product(a2k(b));
			case PLUS: return a2k(a).union(a2k(b));
			case MINUS: return a2k(a).difference(a2k(b));
			default: return null;
			//TODO: IPLUS, IMINUS???
			}
		}
		return null; // Current only UNION, PRODUCT, and DIFFERENCE of Sigs and Fields and ExprConstant.EMPTYNESS are allowed in a defined field's definition.
	}

	/** Return a modifiable TupleSet representing a sound overapproximation of the given expression. */
	TupleSet approximate(Expression expression) {
		return factory.setOf(expression.arity(), Translator.approximate(expression, bounds, solver.options()).denseIndices());
	}

	/** Query the Bounds object to find the lower/upper bound; throws ErrorFatal if expr is not Relation, nor a {union, product} of Relations. */
	TupleSet query(boolean findUpper, Expression expr, boolean makeMutable) throws ErrorFatal {
		if (expr==Relation.NONE) return factory.noneOf(1);
		if (expr==Relation.INTS) return makeMutable ? sigintBounds.clone() : sigintBounds;
		if (expr==KK_SEQIDX) return makeMutable ? seqidxBounds.clone() : seqidxBounds;
		if (expr==KK_STRING) return makeMutable ? stringBounds.clone() : stringBounds;
		if (expr instanceof Relation) {
			TupleSet ans = findUpper ? bounds.upperBound((Relation)expr) : bounds.lowerBound((Relation)expr);
			if (ans!=null) return makeMutable ? ans.clone() : ans;
		}
		else if (expr instanceof BinaryExpression) {
			BinaryExpression b = (BinaryExpression)expr;
			if (b.op() == ExprOperator.UNION) {
				TupleSet left = query(findUpper, b.left(), true);
				TupleSet right = query(findUpper, b.right(), false);
				left.addAll(right);
				return left;
			} else if (b.op() == ExprOperator.PRODUCT) {
				TupleSet left = query(findUpper, b.left(), true);
				TupleSet right = query(findUpper, b.right(), false);
				return left.product(right);
			}
		}
		throw new ErrorFatal("Unknown expression encountered during bounds computation: "+expr);
	}

	/** Shrink the bounds for the given relation; throws an exception if the new bounds is not sameAs/subsetOf the old bounds. */
	void shrink(Relation relation, TupleSet lowerBound, TupleSet upperBound) throws Err {
		if (solved) throw new ErrorFatal("Cannot shrink a Kodkod relation since solve() has completed.");
		TupleSet oldL = bounds.lowerBound(relation);
		TupleSet oldU = bounds.upperBound(relation);
		if (oldU.containsAll(upperBound) && upperBound.containsAll(lowerBound) && lowerBound.containsAll(oldL)) {
			bounds.bound(relation, lowerBound, upperBound);
		} else {
			throw new ErrorAPI("Inconsistent bounds shrinking on relation: "+relation);
		}
	}

	/** Returns the back loop instance of this instance (or -1 if finite). */
	// [HASLab]
	public int getBackLoop() { return backLoop; }

	/** Returns the trace length of this instance. */
	// [HASLab]
	public int getLastTrace() { return traceLength; }

	//===================================================================================================//

	/** Returns true iff the problem has been solved and the result is satisfiable. */
	public boolean satisfiable() { return eval!=null; }

	/** Returns an unmodifiable copy of the list of all sigs in this solution's model; always contains UNIV+SIGINT+SEQIDX+STRING+NONE and has no duplicates. */
	public SafeList<Sig> getAllReachableSigs() { return sigs.dup(); }

	/** Returns an unmodifiable copy of the list of all skolems if the problem is solved and is satisfiable; else returns an empty list. */
	public Iterable<ExprVar> getAllSkolems() { return skolems.dup(); }

	/** Returns an unmodifiable copy of the list of all atoms if the problem is solved and is satisfiable; else returns an empty list. */
	public Iterable<ExprVar> getAllAtoms() { return atoms.dup(); }

	/** Returns the short unique name corresponding to the given atom if the problem is solved and is satisfiable; else returns atom.toString(). */
	String atom2name(Object atom) { String ans=atom2name.get(atom); return ans==null ? atom.toString() : ans; }

	/** Returns the most specific sig corresponding to the given atom if the problem is solved and is satisfiable; else returns UNIV. */
	PrimSig atom2sig(Object atom) { PrimSig sig=atom2sig.get(atom); return sig==null ? UNIV : sig; }

	/** Caches eval(Sig) and eval(Field) results. */
	private Map<Integer,Map<Expr,A4TupleSet>> evalCache = new LinkedHashMap<Integer,Map<Expr,A4TupleSet>>(); // [HASLab]

	/** Return the A4TupleSet for the given sig (if solution not yet solved, or unsatisfiable, or sig not found, then return an empty tupleset). */
	// [HASLab] evals to 0. 
	public A4TupleSet eval(Sig sig) {
		return eval(sig,0);
	}
	
	/** Return the A4TupleSet for the given sig (if solution not yet solved, or unsatisfiable, or sig not found, then return an empty tupleset). */
	// [HASLab] specific state.
	public A4TupleSet eval(Sig sig, int state) {
		try {
			if (!solved || eval==null) return new A4TupleSet(factory.noneOf(1), this);
			if (evalCache.get(state) == null) evalCache.put(state, new LinkedHashMap<Expr, A4TupleSet>()); // [HASLab]
			A4TupleSet ans = evalCache.get(state).get(sig);  // [HASLab]
			if (ans!=null) return ans;
			TupleSet ts = null;
			if (sig.isVariable != null) ts = eval.evaluate((Expression) TranslateAlloyToKodkod.alloy2kodkod(this, sig), state); // [HASLab] 
			else ts = eval.evaluate((Expression) TranslateAlloyToKodkod.alloy2kodkod(this, sig));
			ans = new A4TupleSet(ts, this);
			evalCache.get(state).put(sig, ans);  // [HASLab]
			return ans;
		} catch(Err er) {
			return new A4TupleSet(factory.noneOf(1), this);
		}
	}

	/** Return the A4TupleSet for the given field (if solution not yet solved, or unsatisfiable, or field not found, then return an empty tupleset). */
	// [HASLab] evals to 0. 
	public A4TupleSet eval(Field field) {
		return eval(field,0);
	}
	
	/** Return the A4TupleSet for the given field (if solution not yet solved, or unsatisfiable, or field not found, then return an empty tupleset). */
	// [HASLab] specific state.
	public A4TupleSet eval(Field field, int state) {
		try {
			if (!solved || eval==null) return new A4TupleSet(factory.noneOf(field.type().arity()), this);
			if (evalCache.get(state) == null) evalCache.put(state, new LinkedHashMap<Expr, A4TupleSet>()); // [HASLab]
			A4TupleSet ans = evalCache.get(state).get(field); // [HASLab]
			//if (ans!=null) return ans; 
			TupleSet ts = null;
			if (field.isVariable != null) ts = eval.evaluate((Expression) TranslateAlloyToKodkod.alloy2kodkod(this, field), state); // [HASLab] 
			else ts = eval.evaluate((Expression) TranslateAlloyToKodkod.alloy2kodkod(this, field));
			ans = new A4TupleSet(ts, this);
			evalCache.get(state).put(field, ans);  // [HASLab]
			return ans;
		} catch(Err er) {
			return new A4TupleSet(factory.noneOf(field.type().arity()), this);
		}
	}
	
	/** If this solution is solved and satisfiable, evaluates the given expression at the given state and returns an A4TupleSet, a java Integer, or a java Boolean.*/
	// [HASLab] evals to 0.
	public Object eval(Expr expr) throws Err {
		return eval(expr,0); // [HASLab]
	}
	
	/** If this solution is solved and satisfiable, evaluates the given expression at the given state and returns an A4TupleSet, a java Integer, or a java Boolean.*/
	// [HASLab] specific state. 
	public Object eval(Expr expr, int state) throws Err {
		try {
			if (expr instanceof Sig) return eval((Sig)expr, state); // [HASLab]
			if (expr instanceof Field) return eval((Field)expr, state); // [HASLab]
			if (!solved) throw new ErrorAPI("This solution is not yet solved, so eval() is not allowed.");
			if (eval==null) throw new ErrorAPI("This solution is unsatisfiable, so eval() is not allowed.");
			if (expr.ambiguous && !expr.errors.isEmpty()) expr = expr.resolve(expr.type(), null);
			if (!expr.errors.isEmpty()) throw expr.errors.pick();
			Object result = TranslateAlloyToKodkod.alloy2kodkod(this, expr);
			if (result instanceof IntExpression) return eval.evaluate((IntExpression)result, state) + (eval.wasOverflow() ? " (OF)" : ""); // [HASLab]
			if (result instanceof Formula) return eval.evaluate((Formula)result);
			if (result instanceof Expression) return new A4TupleSet(eval.evaluate((Expression)result, state), this); // [HASLab]
			throw new ErrorFatal("Unknown internal error encountered in the evaluator.");
		} catch(CapacityExceededException ex) {
			throw TranslateAlloyToKodkod.rethrow(ex);
		}
	}

	/** Returns the Kodkod instance represented by this solution; throws an exception if the problem is not yet solved or if it is unsatisfiable. */
	public Instance debugExtractKInstance()  throws Err {
		if (!solved) throw new ErrorAPI("This solution is not yet solved, so instance() is not allowed.");
		if (eval==null) throw new ErrorAPI("This solution is unsatisfiable, so instance() is not allowed.");
		return eval.instance().unmodifiableView();
	}

	//===================================================================================================//

	/** Maps a Kodkod formula to an Alloy Expr or Alloy Pos (or null if no such mapping) */
	Object k2pos(Node formula) { return k2pos.get(formula); }

	/** Associates the Kodkod formula to a particular Alloy Expr (if the Kodkod formula is not already associated with an Alloy Expr or Alloy Pos) */
	Formula k2pos(Formula formula, Expr expr) throws Err {
		if (solved) throw new ErrorFatal("Cannot alter the k->pos mapping since solve() has completed.");
		if (formula==null || expr==null || k2pos.containsKey(formula)) return formula;
		k2pos.put(formula, expr);
		if (formula instanceof BinaryFormula) {
			BinaryFormula b = (BinaryFormula)formula;
			if (b.op() == FormulaOperator.AND) { k2pos(b.left(), expr); k2pos(b.right(), expr); }
		}
		return formula;
	}

	/** Associates the Kodkod formula to a particular Alloy Pos (if the Kodkod formula is not already associated with an Alloy Expr or Alloy Pos) */
	Formula k2pos(Formula formula, Pos pos) throws Err {
		if (solved) throw new ErrorFatal("Cannot alter the k->pos mapping since solve() has completed.");
		if (formula==null || pos==null || pos==Pos.UNKNOWN || k2pos.containsKey(formula)) return formula;
		k2pos.put(formula, pos);
		if (formula instanceof BinaryFormula) {
			BinaryFormula b = (BinaryFormula)formula;
			if (b.op() == FormulaOperator.AND) { k2pos(b.left(), pos); k2pos(b.right(), pos); }
		}
		return formula;
	}

	//===================================================================================================//

	/** Associates the Kodkod relation to a particular Alloy Type (if it is not already associated with something) */
	void kr2type(Relation relation, Type newType) throws Err {
		if (solved) throw new ErrorFatal("Cannot alter the k->type mapping since solve() has completed.");
		if (!rel2type.containsKey(relation)) rel2type.put(relation, newType);
	}

	/** Remove all mapping from Kodkod relation to Alloy Type. */
	void kr2typeCLEAR() throws Err {
		if (solved) throw new ErrorFatal("Cannot clear the k->type mapping since solve() has completed.");
		rel2type.clear();
	}

	//===================================================================================================//

	/** Caches a constant pair of Type.EMPTY and Pos.UNKNOWN */
	private Pair<Type,Pos> cachedPAIR = null;

	/** Maps a Kodkod variable to an Alloy Type and Alloy Pos (if no association exists, it will return (Type.EMPTY , Pos.UNKNOWN) */
	Pair<Type,Pos> kv2typepos(Variable var) {
		Pair<Type,Pos> ans=decl2type.get(var);
		if (ans!=null) return ans;
		if (cachedPAIR==null) cachedPAIR=new Pair<Type,Pos>(Type.EMPTY, Pos.UNKNOWN);
		return cachedPAIR;
	}

	/** Associates the Kodkod variable to a particular Alloy Type and Alloy Pos (if it is not already associated with something) */
	void kv2typepos(Variable var, Type type, Pos pos) throws Err {
		if (solved) throw new ErrorFatal("Cannot alter the k->type mapping since solve() has completed.");
		if (type==null) type=Type.EMPTY;
		if (pos==null) pos=Pos.UNKNOWN;
		if (!decl2type.containsKey(var)) decl2type.put(var, new Pair<Type,Pos>(type, pos));
	}

	//===================================================================================================//

	/** Add the given formula to the list of Kodkod formulas, and associate it with the given Pos object (pos can be null if unknown). */
	void addFormula(Formula newFormula, Pos pos) throws Err {
		if (solved) throw new ErrorFatal("Cannot add an additional formula since solve() has completed.");
		if (formulas.size()>0 && formulas.get(0)==Formula.FALSE) return; // If one formula is false, we don't need the others
		if (newFormula==Formula.FALSE) formulas.clear(); // If one formula is false, we don't need the others
		formulas.add(newFormula);
		if (pos!=null && pos!=Pos.UNKNOWN) k2pos(newFormula, pos);
	}

	/** Add the given formula to the list of Kodkod formulas, and associate it with the given Expr object (expr can be null if unknown) */
	void addFormula(Formula newFormula, Expr expr) throws Err {
		if (solved) throw new ErrorFatal("Cannot add an additional formula since solve() has completed.");
		if (formulas.size()>0 && formulas.get(0)==Formula.FALSE) return; // If one formula is false, we don't need the others
		if (newFormula==Formula.FALSE) formulas.clear(); // If one formula is false, we don't need the others
		formulas.add(newFormula);
		if (expr!=null) k2pos(newFormula, expr);
	}

	/** Set the back loop instant of this instance.*/
	// [HASLab] 
	void setBackLoop(int backloop) {
		this.backLoop = backloop;
	}

	//===================================================================================================//

	/** Helper class that wraps an iterator up where it will pre-fetch the first element (note: it will not prefetch subsequent elements). */
	private static final class Peeker<T> implements Iterator<T> {
		/** The encapsulated iterator. */
		private Iterator<T> iterator;
		/** True iff we have captured the first element. */
		private boolean hasFirst;
		/** If hasFirst is true, then this is the captured first element. */
		private T first;
		/** Constructrs a Peeker object. */
		private Peeker(Iterator<T> it) {
			iterator = it;
			if (it.hasNext()) { hasFirst=true; first=it.next(); }
		}
		/** {@inheritDoc} */
		public boolean hasNext() {
			return hasFirst || iterator.hasNext();
		}
		/** {@inheritDoc} */
		public T next() {
			if (hasFirst) { hasFirst=false; T ans=first; first=null; return ans; } else return iterator.next();
		}
		/** {@inheritDoc} */
		public void remove() { throw new UnsupportedOperationException(); }
	}

	//===================================================================================================//

	/** Helper method to determine if a given binary relation is a total order over a given unary relation. */
	private static List<Tuple> isOrder(TupleSet b, TupleSet u) {
		// Size check
		final int n = u.size();
		final List<Tuple> list = new ArrayList<Tuple>(n);
		if (b.size() == 0 && n <= 1) return list;
		if (b.size() != n-1) return null;
		// Find the starting element
		Tuple head = null;
		TupleSet right = b.project(1);
		for(Tuple x: u) if (!right.contains(x)) {head = x; break;}
		if (head==null) return null;
		final TupleFactory f = head.universe().factory();
		// Form the list
		list.add(head);
		while(true) {
			// Find head.next
			Tuple headnext = null;
			for(Tuple x: b) if (x.atom(0)==head.atom(0)) { headnext = f.tuple(x.atom(1)); break; }
			// If we've reached the end of the chain, and indeed we've formed exactly n elements (and all are in u), we're done
			if (headnext==null) return list.size()==n ? list : null;
			// If we've accumulated more than n elements, or if we reached an element not in u, then we declare failure
			if (list.size()==n || !u.contains(headnext)) return null;
			// Move on to the next step
			head = headnext;
			list.add(head);
		}
	}

	/** Helper method that chooses a name for each atom based on its most specific sig; (external caller should call this method with s==null and nexts==null). */
	// [HASLab] evals to 0.
	private static void rename (A4Solution frame, PrimSig s, Map<Sig,List<Tuple>> nexts, UniqueNameGenerator un) throws Err {
		rename(frame,s,nexts,un,0);
	}

	/** Helper method that chooses a name for each atom based on its most specific sig; (external caller should call this method with s==null and nexts==null). */
	// [HASLab] evals to specific state. 
	private static void rename(A4Solution frame, PrimSig s, Map<Sig,List<Tuple>> nexts, UniqueNameGenerator un, int state) throws Err {
		if (s==null) {
			for(ExprVar sk:frame.skolems) un.seen(sk.label);
			// Store up the skolems
			List<Object> skolems = new ArrayList<Object>();
			for(Map.Entry<Relation,Type> e: frame.rel2type.entrySet()) {
				Relation r = e.getKey(); if (!frame.eval.instance().contains(r)) continue;
				Type t = e.getValue();   if (t.arity() > r.arity()) continue; // Something is wrong; let's skip it
				while (t.arity() < r.arity()) t = UNIV.type().product(t);
				String n = Util.tail(r.name());
				while(n.length()>0 && n.charAt(0)=='$') n = n.substring(1);
				skolems.add(n);
				skolems.add(t);
				skolems.add(r);
			}
			// Find all suitable "next" or "prev" relations
			nexts = new LinkedHashMap<Sig,List<Tuple>>();
			for(Sig sig:frame.sigs) for(Field f: sig.getFields()) if (f.label.compareToIgnoreCase("next")==0) {
				List<List<PrimSig>> fold = f.type().fold();
				if (fold.size()==1) {
					List<PrimSig> t = fold.get(0);
					if (t.size()==3 && t.get(0).isOne!=null && t.get(1)==t.get(2) && !nexts.containsKey(t.get(1))) {
						TupleSet set = frame.eval.evaluate(frame.a2k(t.get(1)));
						if (set.size()<=1) continue;
						TupleSet next = frame.eval.evaluate(frame.a2k(t.get(0)).join(frame.a2k(f)));
						List<Tuple> test = isOrder(next, set);
						if (test!=null) nexts.put(t.get(1), test);
					} else if (t.size()==2 && t.get(0)==t.get(1) && !nexts.containsKey(t.get(0))) {
						TupleSet set = frame.eval.evaluate(frame.a2k(t.get(0)));
						if (set.size()<=1) continue;
						TupleSet next = frame.eval.evaluate(frame.a2k(f));
						List<Tuple> test = isOrder(next, set);
						if (test!=null) nexts.put(t.get(1), test);
					}
				}
			}
			for(Sig sig:frame.sigs) for(Field f: sig.getFields()) if (f.label.compareToIgnoreCase("prev")==0) {
				List<List<PrimSig>> fold = f.type().fold();
				if (fold.size()==1) {
					List<PrimSig> t = fold.get(0);
					if (t.size()==3 && t.get(0).isOne!=null && t.get(1)==t.get(2) && !nexts.containsKey(t.get(1))) {
						TupleSet set = frame.eval.evaluate(frame.a2k(t.get(1)));
						if (set.size()<=1) continue;
						TupleSet next = frame.eval.evaluate(frame.a2k(t.get(0)).join(frame.a2k(f)).transpose());
						List<Tuple> test = isOrder(next, set);
						if (test!=null) nexts.put(t.get(1), test);
					} else if (t.size()==2 && t.get(0)==t.get(1) && !nexts.containsKey(t.get(0))) {
						TupleSet set = frame.eval.evaluate(frame.a2k(t.get(0)));
						if (set.size()<=1) continue;
						TupleSet next = frame.eval.evaluate(frame.a2k(f).transpose());
						List<Tuple> test = isOrder(next, set);
						if (test!=null) nexts.put(t.get(1), test);
					}
				}
			}
			// Assign atom->name and atom->MostSignificantSig
			for(Tuple t:frame.eval.evaluate(Relation.INTS)) { frame.atom2sig.put(t.atom(0), SIGINT); }
			for(Tuple t:frame.eval.evaluate(KK_SEQIDX))     { frame.atom2sig.put(t.atom(0), SEQIDX); }
			for(Tuple t:frame.eval.evaluate(KK_STRING))     { frame.atom2sig.put(t.atom(0), STRING); }
			for(Sig sig:frame.sigs) if (sig instanceof PrimSig && !sig.builtin && ((PrimSig)sig).isTopLevel()) rename(frame, (PrimSig)sig, nexts, un, state); // [HASLab]
			// These are redundant atoms that were not chosen to be in the final instance
			int unused=0;
			for(Tuple tuple:frame.eval.evaluate(Relation.UNIV)) {
				Object atom = tuple.atom(0);
				if (!frame.atom2sig.containsKey(atom)) { frame.atom2name.put(atom, "unused"+unused); unused++; }
			}
			// Add the skolems
			// [HASLab] pessoa: the skolems are only added in the first renaming of a solution
			if (frame.canAddSkolems) {
				for (int num = skolems.size(), i = 0; i < num - 2; i = i + 3) {
					String n = (String) skolems.get(i);
					while (n.length() > 0 && n.charAt(0) == '$') n = n.substring(1);
					Type t = (Type) skolems.get(i + 1);
					Relation r = (Relation) skolems.get(i + 2);
					frame.addSkolem(un.make("$" + n), t, r);
				}
			}
			return;
		}
		if (s.isVariable!=null && s.parent!=UNIV) return; // [HASLab] do not rename variable sigs unless top
		for(PrimSig c: s.children()) rename(frame, c, nexts, un, state); // [HASLab] particular state
		String signame = un.make(s.label.startsWith("this/") ? s.label.substring(5) : s.label);
		List<Tuple> list = new ArrayList<Tuple>();
		for(Tuple t: frame.eval.evaluate(frame.a2k(s), state)) list.add(t); // [HASLab] particular state

		List<Tuple> order = nexts.get(s);
		if (order!=null && order.size()==list.size() && order.containsAll(list)) { list=order; }
        int i = 0;
		for(Tuple t: list) {
			if (frame.atom2sig.containsKey(t.atom(0))) continue; // This means one of the subsig has already claimed this atom.
//			String x = signame + "$" + i;  // [HASLab] do not renumber from 0 due to different states
			String x = t.atom(0)+""; // [HASLab]
			i++;
	        frame.atom2sig.put(t.atom(0), s);
			frame.atom2name.put(t.atom(0), x);
			ExprVar v = ExprVar.make(null, x, s.type());
			TupleSet ts = t.universe().factory().range(t, t);
			Relation r = Relation.unary(x);
			frame.eval.instance().add(r, ts);
			frame.a2k.put(v, r);
			frame.atoms.add(v);
			// [HASLab] pessoa: in this map we adding as the renaming evolves in time the map between a alloy expression and a kk expression
			frame.temporaryA2k.put(v, r);
		}
	}

	//===================================================================================================//

	/** Solve for the solution if not solved already; if cmd==null, we will simply use the lowerbound of each relation as its value. */
	A4Solution solve(final A4Reporter rep, Command cmd, Simplifier simp, boolean tryBookExamples) throws Err, IOException {
		// If already solved, then return this object as is
		if (solved) return this;
		// If cmd==null, then all four arguments are ignored, and we simply use the lower bound of each relation
		if (cmd==null) {
			Instance inst = new Instance(bounds.universe());
			for(int max=max(), i=min(); i<=max; i++) {
				Tuple it = factory.tuple(""+i);
				inst.add(i, factory.range(it, it));
			}
			for(Relation r: bounds.relations()) inst.add(r, bounds.lowerBound(r));
			eval = new Evaluator(inst, solver.options());
			// [HASLab] pessoa: since the atoms' name already are properly renamed, when we are reading a file, it isn't required
			rename(this, null, null, new UniqueNameGenerator());
			solved();
			return this;
		}
		// Otherwise, prepare to do the solve...
		final A4Options opt = originalOptions;
		long time = System.currentTimeMillis();
		rep.debug("Simplifying the bounds...\n");
		if (simp!=null && formulas.size()>0 && !simp.simplify(rep, this, formulas)) addFormula(Formula.FALSE, Pos.UNKNOWN);
		rep.translate(opt.solver.id(), bitwidth, maxseq, solver.options().skolemDepth(), solver.options().symmetryBreaking());
		Formula fgoal = Formula.and(formulas);
		rep.debug("Generating the solution...\n");
		kEnumerator = null;
		Solution sol = null;
		final Reporter oldReporter = solver.options().reporter();
		final boolean solved[] = new boolean[]{true};
		// [HASLab] sl4j reporter
		solver.options().setReporter(new SLF4JReporter() { // Set up a reporter to catch the type+pos of skolems
			@Override public void skolemizing(Decl decl, Relation skolem, List<Decl> predecl) {
				try {
					Type t=kv2typepos(decl.variable()).a;
					if (t==Type.EMPTY) return;
					for(int i=(predecl==null ? -1 : predecl.size()-1); i>=0; i--) {
						Type pp=kv2typepos(predecl.get(i).variable()).a;
						if (pp==Type.EMPTY) return;
						t=pp.product(t);
					}
					kr2type(skolem, t);
				} catch(Throwable ex) { } // Exception here is not fatal
			}
			@Override public void solvingCNF(int primaryVars, int vars, int clauses) {
				if (solved[0]) return; else solved[0]=true; // initially solved[0] is true, so we won't report the # of vars/clauses
				if (rep!=null) rep.solve(primaryVars, vars, clauses);
			}
		});
		// [HASLab] TODO: how to handle non-temporal examples?
//		if (!opt.solver.equals(SatSolver.CNF) && !opt.solver.equals(SatSolver.KK) && tryBookExamples && !isTemporal) { // try book examples
//			A4Reporter r = "yes".equals(System.getProperty("debug")) ? rep : null;
//			try { sol = BookExamples.trial(r, this, fgoal, (Solver) solver, cmd.check); } catch(Throwable ex) { sol = null; }
//		}
		solved[0] = false; // this allows the reporter to report the # of vars/clauses
		for(Relation r: bounds.relations()) { formulas.add(r.eq(r)); } // Without this, kodkod refuses to grow unmentioned relations
		fgoal = Formula.and(formulas);
		// Now pick the solver and solve it!
		if (opt.solver.equals(SatSolver.KK)) {
			File tmpCNF = File.createTempFile("tmp", ".java", new File(opt.tempDirectory));
			String out = tmpCNF.getAbsolutePath();
			Util.writeAll(out, debugExtractKInput());
			rep.resultCNF(out);
			return null;
		}
		if (opt.solver.equals(SatSolver.CNF)) {
			File tmpCNF = File.createTempFile("tmp", ".cnf", new File(opt.tempDirectory));
			String out = tmpCNF.getAbsolutePath();
			solver.options().setSolver(WriteCNF.factory(out));
			try { sol = solver.solve(fgoal, bounds); } catch(WriteCNF.WriteCNFCompleted ex) { rep.resultCNF(out); return null; }
			// The formula is trivial (otherwise, it would have thrown an exception)
			// Since the user wants it in CNF format, we manually generate a trivially satisfiable (or unsatisfiable) CNF file.
			Util.writeAll(out, sol.instance()!=null ? "p cnf 1 1\n1 0\n" : "p cnf 1 2\n1 0\n-1 0\n");
			rep.resultCNF(out);
			return null;
		}
//		if (solver.options().solver()==SATFactory.ZChaffMincost || !solver.options().solver().incremental()) {
//			if (sol==null) sol = solver.solve(fgoal, bounds);
//		} else { // [HASLab] kodkod 2.0+

		rep.debug("eff: "+fgoal.toString());
		rep.debug("eff: "+bounds.toString());
		rep.debug("eff: "+solver.options().toString());
		PardinusBounds b;
		if (solver.options().decomposed())
			b = new PardinusBounds(bounds,true); // [HASLab] support for decomposed
		else b = bounds;
		kEnumerator = new Peeker<Solution>(solver.solveAll(fgoal, b));
		if (sol==null) sol = kEnumerator.next();

//		}
		if (!solved[0]) rep.solve(0, 0, 0);
		final TemporalInstance inst = (TemporalInstance) sol.instance(); // [HASLab]
		// To ensure no more output during SolutionEnumeration
		solver.options().setReporter(oldReporter);
		// If unsatisfiable, then retrieve the unsat core if desired
		if (inst==null && solver.options().solver()==SATFactory.MiniSatProver) {
			try {
				lCore = new LinkedHashSet<Node>();
				Proof p = sol.proof();
				if (sol.outcome()==UNSATISFIABLE) {
					// only perform the minimization if it was UNSATISFIABLE, rather than TRIVIALLY_UNSATISFIABLE
					int i = p.highLevelCore().size();
					rep.minimizing(cmd, i);
					if (opt.coreMinimization==0) try { p.minimize(new RCEStrategy(p.log())); } catch(Throwable ex) {}
					if (opt.coreMinimization==1) try { p.minimize(new HybridStrategy(p.log())); } catch(Throwable ex) {}
					rep.minimized(cmd, i, p.highLevelCore().size());
				}
				for(Iterator<TranslationRecord> it=p.core(); it.hasNext();) {
					Object n=it.next().node();
					if (n instanceof Formula) lCore.add((Formula)n);
				}
				Map<Formula,Node> map = p.highLevelCore();
				hCore = new LinkedHashSet<Node>(map.keySet());
				hCore.addAll(map.values());
			} catch(Throwable ex) {
				lCore = hCore = null;
			}
		}

		// If satisfiable, then add/rename the atoms and skolems
		if (inst!=null) { // [HASLab]
			// [HASLab] pessoa: if the instance is not null, the loop variables are stored, the original instance is saved with
			//the purpose of renaming and the universe' bounds is kept in a Arraylist
			traceLength = inst.end;
			backLoop = inst.loop;
//			Iterator<Object> it = bounds.universe().iterator();
//			while(it.hasNext()) this.universeList.add(it.next());
			instance = inst;
			eval = new Evaluator(inst, solver.options());
			rename(this, null, null, new UniqueNameGenerator());
		}
		// report the result
		solved();
		time = System.currentTimeMillis() - time;
		if (inst!=null) rep.resultSAT(cmd, time, this); else rep.resultUNSAT(cmd, time, this);
		return this;
	}

	// [HASLab] pessoa: structure to execute the renaming as the time evolves
	private Instance instance ;
	private Map<Expr,Expression> originalA2k;
	private Map<Expr,Expression> temporaryA2k =  new HashMap<>();

	// [HASLab] pessoa: boolean var to allow or not add the skolem into the original list from the second renaming
	private boolean canAddSkolems;

	// [HASLab] pessoa: Object of GatherTemporalAtoms class in order to build a xml file with all atoms that appear in the renaming
	public GatherTemporalAtoms temporalAtoms;

	// [HASLab] pessoa: this function performs the renaming of a solution given a particular state.
	// To do that, the control structures are initialised as well as the evaluator with the original instance.
	@Deprecated
	public A4Solution renameTemporal(int state){
		try {
			originalA2k = new HashMap<>();
			for (Expr e : a2k.keySet()){
				if (!this.temporaryA2k.containsKey(e)) this.originalA2k.put(e,a2k.get(e));
			}
			this.a2k =  originalA2k;
			evalCache =  new HashMap<>();
			atoms = new SafeList<ExprVar>();
			atom2name = new LinkedHashMap<Object,String>();
			atom2sig = new LinkedHashMap<Object,PrimSig>();
			eval = new Evaluator(instance, solver.options());
			rename(this, null, null, new UniqueNameGenerator(), state);
			return this;
		} catch (Err err) {
			err.printStackTrace();
		}
		return null;
	}

	//===================================================================================================//

	/** This caches the toString() output. */
	private String toStringCache = null;

	/** Dumps the Kodkod solution into String. */
	@Override public String toString() {
		if (!solved) return "---OUTCOME---\nUnknown.\n";
		if (eval == null) return "---OUTCOME---\nUnsatisfiable.\n";
		String answer = toStringCache;
		if (answer != null) return answer;
		Instance sol = eval.instance();
		StringBuilder sb = new StringBuilder();
        sb.append("---INSTANCE---");
		if (sol instanceof TemporalInstance) {
			sb.append("\nloop=");
			sb.append(((TemporalInstance) sol).loop);
			sb.append("\nend=");
			sb.append(((TemporalInstance) sol).end);
		}
		sb.append("\nintegers={");
		boolean firstTuple = true;
		for (IndexedEntry<TupleSet> e : sol.intTuples()) {
			if (firstTuple)
				firstTuple = false;
			else
				sb.append(", ");
			// No need to print e.index() since we've ensured the Int atom's
			// String representation is always equal to ""+e.index()
			Object atom = e.value().iterator().next().atom(0);
			sb.append(atom2name(atom));
		}
		sb.append("}\n");
		if (sol instanceof TemporalInstance) {
			for (int i = 0; i <= ((TemporalInstance) sol).end; i++) { // [HASLab]
				sb.append("------State " + i + "-------\n");
				this.renameTemporal(i);
				try {
					for (Sig s : sigs) {
						sb.append(s.label).append("=").append(eval(s, i)).append("\n");
						for (Field f : s.getFields())
							sb.append(s.label).append("<:").append(f.label).append("=").append(eval(f, i)).append("\n");
					}
					for (ExprVar v : skolems) {
						sb.append("skolem ").append(v.label).append("=").append(eval(v, i)).append("\n");
					}
				} catch (Err er) {
					return toStringCache = ("<Evaluator error occurred at Time " + i + " : " + er + ">");
				}
			}
		} else {
			try {
				for (Sig s : sigs) {
					sb.append(s.label).append("=").append(eval(s)).append("\n");
					for (Field f : s.getFields())
						sb.append(s.label).append("<:").append(f.label).append("=").append(eval(f)).append("\n");
				}
				for (ExprVar v : skolems) {
					sb.append("skolem ").append(v.label).append("=").append(eval(v)).append("\n");
				}
			} catch (Err er) {
				return toStringCache = ("<Evaluator error occurred: " + er + ">");
			}
}
		return toStringCache = sb.toString();
	}

	//===================================================================================================//

	/** If nonnull, it caches the result of calling "next()". */
	private A4Solution nextCache = null;

	/** If this solution is UNSAT, return itself; else return the next solution (which could be SAT or UNSAT).
	 * @throws ErrorAPI if the solver was not an incremental solver
	 */
	public A4Solution next() throws Err {
		if (!solved) throw new ErrorAPI("This solution is not yet solved, so next() is not allowed.");
		if (eval==null) return this;
		if (nextCache==null) nextCache=new A4Solution(this);
		return nextCache;
	}

	/** Returns true if this solution was generated by an incremental SAT solver. */
	public boolean isIncremental() { return kEnumerator!=null; }

	//===================================================================================================//

	/** The low-level unsat core; null if it is not available. */
	private LinkedHashSet<Node> lCore = null;

	/** This caches the result of lowLevelCore(). */
	private Set<Pos> lCoreCache = null;

	/** If this solution is unsatisfiable and its unsat core is available, then return the core; else return an empty set. */
	public Set<Pos> lowLevelCore() {
		if (lCoreCache!=null) return lCoreCache;
		Set<Pos> ans1 = new LinkedHashSet<Pos>();
		if (lCore!=null) for(Node f: lCore) {
			Object y = k2pos(f);
			if (y instanceof Pos) ans1.add( (Pos)y ); else if (y instanceof Expr) ans1.add( ((Expr)y).span() );
		}
		return lCoreCache = Collections.unmodifiableSet(ans1);
	}

	//===================================================================================================//

	/** The high-level unsat core; null if it is not available. */
	private LinkedHashSet<Node> hCore = null;

	/** This caches the result of highLevelCore(). */
	private Pair<Set<Pos>,Set<Pos>> hCoreCache = null;

	/** If this solution is unsatisfiable and its unsat core is available, then return the core; else return an empty set. */
	public Pair<Set<Pos>,Set<Pos>> highLevelCore() {
		if (hCoreCache!=null) return hCoreCache;
		Set<Pos> ans1 = new LinkedHashSet<Pos>(), ans2 = new LinkedHashSet<Pos>();
		if (hCore!=null) for(Node f: hCore) {
			Object x = k2pos(f);
			if (x instanceof Pos) {
				// System.out.println("F: "+f+" at "+x+"\n"); System.out.flush();
				ans1.add((Pos)x);
			} else if (x instanceof Expr) {
				Expr expr = (Expr)x;
				Pos p = ((Expr)x).span();
				ans1.add(p);
				// System.out.println("F: "+f+" by "+p.x+","+p.y+"->"+p.x2+","+p.y2+" for "+x+"\n\n"); System.out.flush();
				for(Func func: expr.findAllFunctions()) ans2.add(func.getBody().span());
			}
		}
		return hCoreCache = new Pair<Set<Pos>,Set<Pos>>(Collections.unmodifiableSet(ans1), Collections.unmodifiableSet(ans2));
	}

	//===================================================================================================//

	/** Helper method to write out a full XML file. */
	public void writeXML(String filename) throws Err {
		writeXML(filename, null, null);
	}

	/** Helper method to write out a full XML file. */
	// [HASLab] evals to specific state.
	public void writeXML(String filename, int state) throws Err {
		writeXML(filename, null, null, state);
	}

	/** Helper method to write out a full XML file. */
	public void writeXML(String filename, Iterable<Func> macros) throws Err {
		writeXML(filename, macros, null);
	}
	
	/** Helper method to write out a full XML file.*/
	// [HASLab] evals to 0. 
	public void writeXML(String filename, Iterable<Func> macros, Map<String,String> sourceFiles) throws Err {
		writeXML(filename, macros, sourceFiles, 0);
	}

	/** Helper method to write out a full XML file.*/
	// [HASLab] evals to specific state.
	public void writeXML(String filename, Iterable<Func> macros, Map<String,String> sourceFiles, int state) throws Err {
		PrintWriter out=null;
		try {
			out=new PrintWriter(filename,"UTF-8");
			writeXML(out, macros, sourceFiles, state); // [HASLab]
			if (!Util.close(out)) throw new ErrorFatal("Error writing the solution XML file.");
		} catch(IOException ex) {
			Util.close(out);
			throw new ErrorFatal("Error writing the solution XML file.", ex);
		}
	}

	/** Helper method to write out a full XML file. */
	// [HASLab] evals to specific state.
	public void writeXML(A4Reporter rep, String filename, Iterable<Func> macros, Map<String,String> sourceFiles, int state) throws Err {
		PrintWriter out=null;
		try {
			out=new PrintWriter(filename,"UTF-8");
			writeXML(rep, out, macros, sourceFiles, state); // [HASLab]
			if (!Util.close(out)) throw new ErrorFatal("Error writing the solution XML file.");
		} catch(IOException ex) {
			Util.close(out);
			throw new ErrorFatal("Error writing the solution XML file.", ex);
		}
	}

	/** Helper method to write out a full XML file. */
	// [HASLab] evals to 0. 
	public void writeXML(PrintWriter writer, Iterable<Func> macros, Map<String,String> sourceFiles) throws Err {
		writeXML(writer, macros, sourceFiles, 0);
	}
	
	/** Helper method to write out a full XML file. */
	// [HASLab] evals to specific state. 
	public void writeXML(PrintWriter writer, Iterable<Func> macros, Map<String,String> sourceFiles, int state) throws Err {
		A4SolutionWriter.writeInstance(null, this, writer, macros, sourceFiles, state);
		if (writer.checkError()) throw new ErrorFatal("Error writing the solution XML file.");
	}

	/** Helper method to write out a full XML file. */
	// [HASLab] evals to specific state.
	public void writeXML(A4Reporter rep, PrintWriter writer, Iterable<Func> macros, Map<String,String> sourceFiles, int state) throws Err {
		A4SolutionWriter.writeInstance(rep, this, writer, macros, sourceFiles, state);
		if (writer.checkError()) throw new ErrorFatal("Error writing the solution XML file.");
	}
	
}
