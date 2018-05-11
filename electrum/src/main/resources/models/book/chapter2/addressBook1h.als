module tour/addressBook1h ------- Page 14..16

sig Name, Addr { }

sig Book {
	addr: Name -> lone Addr
}

pred show [b: Book] {
	#b.addr > 1
	#Name.(b.addr) > 1
}
run show for 3 but 1 Book

pred add [b, b1: Book, n: Name, a: Addr] {
	b1.addr = b.addr + n->a
}

pred del [b, b1: Book, n: Name] {
	b1.addr = b.addr - n->Addr
}

fun lookup [b: Book, n: Name] : set Addr {
	n.(b.addr)
}

pred showAdd [b, b1: Book, n: Name, a: Addr] {
	add [b, b1, n, a]
	#Name.(b1.addr) > 1
}
run showAdd for 3 but 2 Book

assert delUndoesAdd {
	all b, b1, b2: Book, n: Name, a: Addr |
		no n.(b.addr) and add [b, b1, n, a] and del [b1, b2, n]
		implies
		b.addr = b2.addr
}

assert addIdempotent {
	all b, b1, b2: Book, n: Name, a: Addr |
		add [b, b1, n, a] and add [b1, b2, n, a]
		implies
		b1.addr = b2.addr
}

assert addLocal {
	all b, b1: Book, n, n1: Name, a: Addr |
		add [b, b1, n, a] and n != n1
		implies
		lookup [b, n1] = lookup [b1, n1]
}

// This command should not find any counterexample.
check delUndoesAdd for 3

// This command should not find any counterexample.
check delUndoesAdd for 10 but 3 Book

// This command should not find any counterexample.
check addIdempotent for 3

// This command should not find any counterexample.
check addLocal for 3 but 2 Book
