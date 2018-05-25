module tour/addressBook3a ----- Page 25

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

pred add [b, b1: Book, n: Name, t: Target] { b1.addr = b.addr + n->t }
pred del [b, b1: Book, n: Name, t: Target] { b1.addr = b.addr - n->t }
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

pred show { }

// This command generates an instance similar to Fig 2.15
run show for 4
