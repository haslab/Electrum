module tour/addressBook3d ----- this is the final model in fig 2.18

open util/ordering [Book] as BookOrder

abstract sig Target { }
sig Addr extends Target { }
abstract sig Name extends Target { }

sig Alias, Group extends Name { }

sig Book {
	names: set Name,
	addr: names->some Target
} {
	no n: Name | n in n.^addr
	all a: Alias | lone a.addr
}

pred add [b, b1: Book, n: Name, t: Target] {
	t in Addr or some lookup [b, Name&t]
	b1.addr = b.addr + n->t
}

pred del [b, b1: Book, n: Name, t: Target] {
	no b.addr.n or some n.(b.addr) - t
	b1.addr = b.addr - n->t
}

fun lookup [b: Book, n: Name] : set Addr { n.^(b.addr) & Addr }

pred init [b: Book]  { no b.addr }

fact traces {
	init [first]
	all b: Book-last |
	  let b1 = b.next |
	    some n: Name, t: Target |
	      add [b, b1, n, t] or del [b, b1, n, t]
}

------------------------------------------------------

assert delUndoesAdd {
	all b, b1, b2: Book, n: Name, t: Target |
		no n.(b.addr) and add [b, b1, n, t] and del [b1, b2, n, t]
		implies
		b.addr = b2.addr
}

// This should not find any counterexample.
check delUndoesAdd for 3

------------------------------------------------------

assert addIdempotent {
	all b, b1, b2: Book, n: Name, t: Target |
		add [b, b1, n, t] and add [b1, b2, n, t]
		implies
		b1.addr = b2.addr
}

// This should not find any counterexample.
check addIdempotent for 3

------------------------------------------------------

assert addLocal {
	all b, b1: Book, n, n1: Name, t: Target |
		add [b, b1, n, t] and n != n1
		implies
		lookup [b, n1] = lookup [b1, n1]
}

// This should not find any counterexample.
check addLocal for 3 but 2 Book

------------------------------------------------------

assert lookupYields {
	all b: Book, n: b.names | some lookup [b,n]
}

// This should not find any counterexample.
check lookupYields for 3 but 4 Book

// This should not find any counterexample.
check lookupYields for 6
