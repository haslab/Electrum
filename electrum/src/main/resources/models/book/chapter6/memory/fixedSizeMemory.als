module chapter6/memory/fixedSizeMemory [Addr, Data]

sig Memory {
	data: Addr -> one Data	
	}

pred init [m: Memory] {
	// This predicate is empty in order to allow non-deterministic initialization
	}

pred write [m, m1: Memory, a: Addr, d: Data] {
	m1.data = m.data ++ a -> d
	}

pred read [m: Memory, a: Addr, d: Data] {
	d = m.data [a]
	}

fact Canonicalize {
	no disj m, m1: Memory | m.data = m1.data
	}
