module chapter5/addressBook --- the model in fig 5.1

abstract sig Target {}

sig Addr extends Target {}
sig Name extends Target {}
sig Book {addr: Name -> Target}

fact Acyclic {all b: Book | no n: Name | n in n.^(b.addr)}

pred add [b, b1: Book, n: Name, t: Target] {
	b1.addr = b.addr + n -> t
	}

// This command should produce an instance similar to Fig 5.2
run add for 3 but 2 Book

fun lookup [b: Book, n: Name]: set Addr {n.^(b.addr) & Addr}

assert addLocal {
	all b,b1: Book, n,n1: Name, t: Target |
		add [b,b1,n,t] and n != n1 => lookup [b,n1] = lookup [b1,n1]
	}

// This command should produce a counterexample similar to Fig 5.3
check addLocal for 3 but 2 Book
