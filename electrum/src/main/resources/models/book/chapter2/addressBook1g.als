module tour/addressBook1g ----- Page 14

sig Name, Addr { }

sig Book {
	addr: Name -> lone Addr
}

pred add [b, b1: Book, n: Name, a: Addr] {
	b1.addr = b.addr + n->a
}

pred del [b, b1: Book, n: Name] {
	b1.addr = b.addr - n->Addr
}

fun lookup [b: Book, n: Name] : set Addr {
	n.(b.addr)
}

assert delUndoesAdd {
	all b, b1, b2: Book, n: Name, a: Addr |
		add [b, b1, n, a] and del [b1, b2, n]
		implies
		b.addr = b2.addr
}

// This command generates an instance similar to Fig 2.6
check delUndoesAdd for 3
