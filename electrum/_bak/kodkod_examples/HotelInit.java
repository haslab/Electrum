package kodkod_examples;

import java.util.Arrays;
import java.util.Iterator;
import java.util.List;

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
    (all this: this/Room | 
      (this . this/Room.keys) in this/Key) && 
    (this/Room.keys . univ) in this/Room && 
    (all this: this/Room | 
      one (this . this/Room.currentKey) && 
      (this . this/Room.currentKey) in (this . this/Room.keys)) && 
    (this/Room.currentKey . univ) in this/Room && 
    (this/FrontDesk . (this/FrontDesk -> this/FrontDesk.lastKey)) in (this/Room -> 
    this/Key) && 
    (all v939: this/Room | 
      lone (v939 . (this/FrontDesk . (this/FrontDesk -> this/FrontDesk.lastKey))
      ) && 
      (v939 . (this/FrontDesk . (this/FrontDesk -> this/FrontDesk.lastKey))) in 
      this/Key) && 
    (all v940: this/Key | 
      ((this/FrontDesk . (this/FrontDesk -> this/FrontDesk.lastKey)) . v940) in 
      this/Room) && 
    (this/FrontDesk . (this/FrontDesk -> this/FrontDesk.occupant)) in (this/Room -> 
    this/Guest) && 
    (all this: this/Guest | 
      (this . this/Guest.gKeys) in this/Key) && 
    (this/Guest.gKeys . univ) in this/Guest && 
    (ko/Ord . (ko/Ord -> ko/Ord.First)) in this/Key && 
    (ko/Ord . (ko/Ord -> ko/Ord.Next)) in (this/Key -> this/Key) && 
    ord[ko/Ord.Next, this/Key, ko/Ord.First, ] && 
    this/Room.keys in (this/Room -> this/Key) && 
    (all v941: this/Room | 
      (v941 . this/Room.keys) in this/Key) && 
    (all v942: this/Key | 
      lone (this/Room.keys . v942) && 
      (this/Room.keys . v942) in this/Room) && 
    no (this/Guest . this/Guest.gKeys) && 
    no this/FrontDesk.occupant && 
    (all init_r: this/Room | 
      (init_r . this/FrontDesk.lastKey) = (init_r . this/Room.currentKey)) && 
    Int/next = Int/next && 
    seq/Int = seq/Int && 
    String = String && 
    this/Key = this/Key && 
    this/Room = this/Room && 
    this/FrontDesk = this/FrontDesk && 
    this/Guest = this/Guest && 
    ko/Ord = ko/Ord && 
    this/Room.keys = this/Room.keys && 
    this/Room.currentKey = this/Room.currentKey && 
    this/FrontDesk.lastKey = this/FrontDesk.lastKey && 
    this/FrontDesk.occupant = this/FrontDesk.occupant && 
    this/Guest.gKeys = this/Guest.gKeys && 
    ko/Ord.First = ko/Ord.First && 
    ko/Ord.Next = ko/Ord.Next && 
     = 
  ==================================================
*/
public final class HotelInit {

public static void main(String[] args) throws Exception {

Relation x0 = Relation.nary("Int/next", 2);
Relation x1 = Relation.unary("seq/Int");
Relation x2 = Relation.unary("String");
Relation key = Relation.unary("this/Key");
Relation room = Relation.unary("this/Room");
Relation frontdesk = Relation.unary("this/FrontDesk");
Relation guest = Relation.unary("this/Guest");
Relation x7 = Relation.unary("ko/Ord");
Relation keys = Relation.nary("this/Room.keys", 2);
Relation currentkey = Relation.nary("this/Room.currentKey", 2);
Relation lastkey = Relation.nary("this/FrontDesk.lastKey", 2);
Relation occupant = Relation.nary("this/FrontDesk.occupant", 2);
Relation x12 = Relation.nary("this/Guest.gKeys", 2);
Relation x13 = Relation.unary("ko/Ord.First");
Relation x14 = Relation.nary("ko/Ord.Next", 2);
Relation x15 = Relation.unary("");

List<String> atomlist = Arrays.asList(
 "FrontDesk$0", "Guest$0", "Key$0", "Key$1", "Key$2",
 "Room$0", "ko/Ord$0"
);

Universe universe = new Universe(atomlist);
TupleFactory factory = universe.factory();
Bounds bounds = new Bounds(universe);

TupleSet x0_upper = factory.noneOf(2);
bounds.boundExactly(x0, x0_upper);

TupleSet x1_upper = factory.noneOf(1);
bounds.boundExactly(x1, x1_upper);

TupleSet x2_upper = factory.noneOf(1);
bounds.boundExactly(x2, x2_upper);

TupleSet x3_upper = factory.noneOf(1);
x3_upper.add(factory.tuple("Key$0"));
x3_upper.add(factory.tuple("Key$1"));
x3_upper.add(factory.tuple("Key$2"));
bounds.boundExactly(key, x3_upper);

TupleSet x4_upper = factory.noneOf(1);
x4_upper.add(factory.tuple("Room$0"));
bounds.boundExactly(room, x4_upper);

TupleSet x5_upper = factory.noneOf(1);
x5_upper.add(factory.tuple("FrontDesk$0"));
bounds.boundExactly(frontdesk, x5_upper);

TupleSet x6_upper = factory.noneOf(1);
x6_upper.add(factory.tuple("Guest$0"));
bounds.boundExactly(guest, x6_upper);

TupleSet x7_upper = factory.noneOf(1);
x7_upper.add(factory.tuple("ko/Ord$0"));
bounds.boundExactly(x7, x7_upper);

TupleSet x8_upper = factory.noneOf(2);
x8_upper.add(factory.tuple("Room$0").product(factory.tuple("Key$0")));
x8_upper.add(factory.tuple("Room$0").product(factory.tuple("Key$1")));
x8_upper.add(factory.tuple("Room$0").product(factory.tuple("Key$2")));
bounds.bound(keys, x8_upper);

TupleSet x9_upper = factory.noneOf(2);
x9_upper.add(factory.tuple("Room$0").product(factory.tuple("Key$0")));
x9_upper.add(factory.tuple("Room$0").product(factory.tuple("Key$1")));
x9_upper.add(factory.tuple("Room$0").product(factory.tuple("Key$2")));
bounds.bound(currentkey, x9_upper);

TupleSet x10_upper = factory.noneOf(2);
x10_upper.add(factory.tuple("Room$0").product(factory.tuple("Key$0")));
x10_upper.add(factory.tuple("Room$0").product(factory.tuple("Key$1")));
x10_upper.add(factory.tuple("Room$0").product(factory.tuple("Key$2")));
bounds.bound(lastkey, x10_upper);

TupleSet x11_upper = factory.noneOf(2);
x11_upper.add(factory.tuple("Room$0").product(factory.tuple("Guest$0")));
bounds.bound(occupant, x11_upper);

TupleSet x12_upper = factory.noneOf(2);
x12_upper.add(factory.tuple("Guest$0").product(factory.tuple("Key$0")));
x12_upper.add(factory.tuple("Guest$0").product(factory.tuple("Key$1")));
x12_upper.add(factory.tuple("Guest$0").product(factory.tuple("Key$2")));
bounds.bound(x12, x12_upper);

TupleSet x13_upper = factory.noneOf(1);
x13_upper.add(factory.tuple("Key$0"));
x13_upper.add(factory.tuple("Key$1"));
x13_upper.add(factory.tuple("Key$2"));
bounds.bound(x13, x13_upper);

TupleSet x14_upper = factory.noneOf(2);
x14_upper.add(factory.tuple("Key$0").product(factory.tuple("Key$0")));
x14_upper.add(factory.tuple("Key$0").product(factory.tuple("Key$1")));
x14_upper.add(factory.tuple("Key$0").product(factory.tuple("Key$2")));
x14_upper.add(factory.tuple("Key$1").product(factory.tuple("Key$0")));
x14_upper.add(factory.tuple("Key$1").product(factory.tuple("Key$1")));
x14_upper.add(factory.tuple("Key$1").product(factory.tuple("Key$2")));
x14_upper.add(factory.tuple("Key$2").product(factory.tuple("Key$0")));
x14_upper.add(factory.tuple("Key$2").product(factory.tuple("Key$1")));
x14_upper.add(factory.tuple("Key$2").product(factory.tuple("Key$2")));
bounds.bound(x14, x14_upper);

TupleSet x15_upper = factory.noneOf(1);
x15_upper.add(factory.tuple("Key$0"));
x15_upper.add(factory.tuple("Key$1"));
x15_upper.add(factory.tuple("Key$2"));
bounds.bound(x15, x15_upper);


Variable x19=Variable.unary("this");
Decls x18=x19.oneOf(room);
Expression x21=x19.join(keys);
Formula x20=x21.in(key);
Formula x17=x20.forAll(x18);
Expression x23=keys.join(Expression.UNIV);
Formula x22=x23.in(room);
Variable x27=Variable.unary("this");
Decls x26=x27.oneOf(room);
Expression x30=x27.join(currentkey);
Formula x29=x30.one();
Expression x32=x27.join(keys);
Formula x31=x30.in(x32);
Formula x28=x29.and(x31);
Formula x25=x28.forAll(x26);
Expression x34=currentkey.join(Expression.UNIV);
Formula x33=x34.in(room);
Expression x39=frontdesk.product(lastkey);
Expression x38=frontdesk.join(x39);
Expression x40=room.product(key);
Formula x37=x38.in(x40);
Variable x43=Variable.unary("v983");
Decls x42=x43.oneOf(room);
Expression x46=x43.join(x38);
Formula x45=x46.lone();
Formula x47=x46.in(key);
Formula x44=x45.and(x47);
Formula x41=x44.forAll(x42);
Formula x36=x37.and(x41);
Variable x50=Variable.unary("v984");
Decls x49=x50.oneOf(key);
Expression x52=x38.join(x50);
Formula x51=x52.in(room);
Formula x48=x51.forAll(x49);
Formula x35=x36.and(x48);
Expression x55=frontdesk.product(occupant);
Expression x54=frontdesk.join(x55);
Expression x56=room.product(guest);
Formula x53=x54.in(x56);
Variable x59=Variable.unary("this");
Decls x58=x59.oneOf(guest);
Expression x61=x59.join(x12);
Formula x60=x61.in(key);
Formula x57=x60.forAll(x58);
Expression x63=x12.join(Expression.UNIV);
Formula x62=x63.in(guest);
Expression x66=x7.product(x13);
Expression x65=x7.join(x66);
Formula x64=x65.in(key);
Expression x69=x7.product(x14);
Expression x68=x7.join(x69);
Expression x70=key.product(key);
Formula x67=x68.in(x70);
Formula x71=x14.totalOrder(key,x13,x15);
Expression x75=room.product(key);
Formula x74=keys.in(x75);
Variable x78=Variable.unary("v985");
Decls x77=x78.oneOf(room);
Expression x80=x78.join(keys);
Formula x79=x80.in(key);
Formula x76=x79.forAll(x77);
Formula x73=x74.and(x76);
Variable x83=Variable.unary("v986");
Decls x82=x83.oneOf(key);
Expression x86=keys.join(x83);
Formula x85=x86.lone();
Formula x87=x86.in(room);
Formula x84=x85.and(x87);
Formula x81=x84.forAll(x82);
Formula x72=x73.and(x81);
Expression x91=guest.join(x12);
Formula x90=x91.no();
Formula x92=occupant.no();
Formula x89=x90.and(x92);
Variable x95=Variable.unary("init_r");
Decls x94=x95.oneOf(room);
Expression x97=x95.join(lastkey);
Expression x98=x95.join(currentkey);
Formula x96=x97.eq(x98);
Formula x93=x96.forAll(x94);
Formula x88=x89.and(x93);
Formula x99=x0.eq(x0);
Formula x100=x1.eq(x1);
Formula x101=x2.eq(x2);
Formula x102=key.eq(key);
Formula x103=room.eq(room);
Formula x104=frontdesk.eq(frontdesk);
Formula x105=guest.eq(guest);
Formula x106=x7.eq(x7);
Formula x107=keys.eq(keys);
Formula x108=currentkey.eq(currentkey);
Formula x109=lastkey.eq(lastkey);
Formula x110=occupant.eq(occupant);
Formula x111=x12.eq(x12);
Formula x112=x13.eq(x13);
Formula x113=x14.eq(x14);
Formula x114=x15.eq(x15);
Formula x16=Formula.compose(FormulaOperator.AND, x17, x22, x25, x33, x35, x53, x57, x62, x64, x67, x71, x72, x88, x99, x100, x101, x102, x103, x104, x105, x106, x107, x108, x109, x110, x111, x112, x113, x114);

	Solver solver = new Solver();
	solver.options().setSolver(SATFactory.DefaultSAT4J);
	solver.options().setBitwidth(1);
	solver.options().setFlatten(false);
	solver.options().setIntEncoding(Options.IntEncoding.TWOSCOMPLEMENT);
	solver.options().setSymmetryBreaking(20);
	solver.options().setSkolemDepth(0);
//	solver.options().setNoOverflow(true);
	System.out.println("Solving...");
	System.out.flush();
	long startTime = System.currentTimeMillis();
	Iterator<Solution> sols = solver.solveAll(x16,bounds);
	int i = 1;
	while (sols.hasNext()) {
		Solution sol = sols.next();
		System.out.println(i+":"+sol.toString());
		i++;
	}
	long endTime = System.currentTimeMillis();
	System.out.println((endTime-startTime)+"ms");
	}

}
