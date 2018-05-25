package kodkod_examples;

import java.util.ArrayList;
import java.util.Iterator;

import kodkod.ast.Decls;
import kodkod.ast.Expression;
import kodkod.ast.Formula;
import kodkod.ast.Relation;
import kodkod.ast.Variable;
import kodkod.ast.operator.FormulaOperator;
import kodkod.engine.Solution;
import kodkod.engine.Solver;
import kodkod.engine.config.Options;
import kodkod.engine.satlab.SATFactory;
import kodkod.instance.Bounds;
import kodkod.instance.TupleFactory;
import kodkod.instance.TupleSet;
import kodkod.instance.Universe;

/* 
  ==================================================
    kodkod formula: 
  ==================================================
    this/elected in this/Process && 
    (all this: this/Process | 
      one (this . this/Process.succ) && 
      (this . this/Process.succ) in this/Process) && 
    (this/Process.succ . univ) in this/Process && 
    (all this: this/Process | 
      (this . this/Process.toSend) in this/Process) && 
    (this/Process.toSend . univ) in this/Process && 
    (PO/Ord . (PO/Ord -> PO/Ord.First)) in this/Process && 
    (PO/Ord . (PO/Ord -> PO/Ord.Next)) in (this/Process -> this/Process) && 
    ord[PO/Ord.Next, this/Process, PO/Ord.First, ] && 
    (all p: this/Process | 
      this/Process in (p . ^this/Process.succ)) && 
    (all p: this/Process | 
      (p . this/Process.toSend) = p) && 
    Int/next = Int/next && 
    seq/Int = seq/Int && 
    String = String && 
    this/Process = this/Process && 
    PO/Ord = PO/Ord && 
    this/elected = this/elected && 
    this/Process.succ = this/Process.succ && 
    this/Process.toSend = this/Process.toSend && 
    PO/Ord.First = PO/Ord.First && 
    PO/Ord.Next = PO/Ord.Next && 
     = 
  ==================================================
*/
public final class ElectionInit {

public static void main(String[] args) throws Exception {

	int n = 3;
	
Relation x0 = Relation.nary("Int/next", 2);
Relation x1 = Relation.unary("seq/Int");
Relation x2 = Relation.unary("String");
Relation process = Relation.unary("Process");
Relation x4 = Relation.unary("PO/Ord");
Relation succ = Relation.nary("succ", 2);
Relation toSend = Relation.nary("toSend", 2);
Relation first = Relation.unary("PO/Ord.First");
Relation next = Relation.nary("PO/Ord.Next", 2);
Relation x10 = Relation.unary("");

ArrayList<String> atomlist = new ArrayList<String>();

atomlist.add("PO/Ord$0");

for (int i = 0;i<n;i++)
	atomlist.add("P"+i);


Universe universe = new Universe(atomlist);
TupleFactory factory = universe.factory();
Bounds bounds = new Bounds(universe);

TupleSet x0_upper = factory.noneOf(2);
bounds.boundExactly(x0, x0_upper);

TupleSet x1_upper = factory.noneOf(1);
bounds.boundExactly(x1, x1_upper);

TupleSet x2_upper = factory.noneOf(1);
bounds.boundExactly(x2, x2_upper);

TupleSet process_upper = factory.noneOf(1);
for (int i = 0; i < n; i++)
	process_upper.add(factory.tuple("P"+i));
bounds.boundExactly(process, process_upper);

TupleSet x4_upper = factory.noneOf(1);
x4_upper.add(factory.tuple("PO/Ord$0"));
bounds.boundExactly(x4, x4_upper);



TupleSet succ_upper = factory.noneOf(2);
for (int i = 0; i < n; i++)
	for (int j = 0; j < n; j++)
		succ_upper.add(factory.tuple("P"+i).product(factory.tuple("P"+j)));
bounds.bound(succ, succ_upper);

TupleSet toSend_upper = factory.noneOf(2);
for (int i = 0; i < n; i++)
	for (int j = 0; j < n; j++)
		toSend_upper.add(factory.tuple("P"+i).product(factory.tuple("P"+j)));
bounds.bound(toSend, toSend_upper);

TupleSet first_upper = factory.noneOf(1);
for (int i = 0; i < n; i++)
	first_upper.add(factory.tuple("P"+i));
bounds.bound(first, first_upper);

TupleSet next_upper = factory.noneOf(2);
for (int i = 0; i < n; i++)
	for (int j = 0; j < n; j++)
		next_upper.add(factory.tuple("P"+i).product(factory.tuple("P"+j)));
bounds.bound(next, next_upper);

TupleSet x10_upper = factory.noneOf(1);
for (int i = 0; i < n; i++)
	x10_upper.add(factory.tuple("P"+i));
bounds.bound(x10, x10_upper);


Variable x15=Variable.unary("this");
Decls x14=x15.oneOf(process);
Expression x18=x15.join(succ);
Formula x17=x18.one();
Formula x19=x18.in(process);
Formula x16=x17.and(x19);
Formula x13=x16.forAll(x14);
Expression x21=succ.join(Expression.UNIV);
Formula x20=x21.in(process);
Variable x25=Variable.unary("this");
Decls x24=x25.oneOf(process);
Expression x27=x25.join(toSend);
Formula x26=x27.in(process);
Formula x23=x26.forAll(x24);
Expression x29=toSend.join(Expression.UNIV);
Formula x28=x29.in(process);
Expression x32=x4.product(first);
Expression x31=x4.join(x32);
Formula x30=x31.in(process);
Expression x35=x4.product(next);
Expression x34=x4.join(x35);
Expression x36=process.product(process);
Formula x33=x34.in(x36);
Formula x37=next.totalOrder(process,first,x10);
Variable x40=Variable.unary("p");
Decls x39=x40.oneOf(process);
Expression x43=succ.closure();
Expression x42=x40.join(x43);
Formula x41=process.in(x42);
Formula x38=x41.forAll(x39);
Variable x46=Variable.unary("p");
Decls x45=x46.oneOf(process);
Expression x48=x46.join(toSend);
Formula x47=x48.eq(x46);
Formula x44=x47.forAll(x45);
Formula x49=x0.eq(x0);
Formula x50=x1.eq(x1);
Formula x51=x2.eq(x2);
Formula x52=process.eq(process);
Formula x53=x4.eq(x4);
Formula x55=succ.eq(succ);
Formula x56=toSend.eq(toSend);
Formula x57=first.eq(first);
Formula x58=next.eq(next);
Formula x59=x10.eq(x10);
Formula x11=Formula.compose(FormulaOperator.AND, x13, x20, x23, x28, x30, x33, x37, x38, x44, x49, x50, x51, x52, x53, x55, x56, x57, x58, x59);

Solver solver = new Solver();
solver.options().setSolver(SATFactory.DefaultSAT4J);
solver.options().setBitwidth(1);
solver.options().setFlatten(false);
solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
solver.options().setSymmetryBreaking(20);
solver.options().setSkolemDepth(0);
System.out.println("Solving...");
System.out.flush();
long startTime = System.currentTimeMillis();
Iterator<Solution> sols = solver.solveAll(x11,bounds);
//while (sols.hasNext()) {
	Solution sol = sols.next();
	System.out.println(sol.toString());
//}
long endTime = System.currentTimeMillis();
System.out.println((endTime-startTime)/1000.0+"s");
}}
