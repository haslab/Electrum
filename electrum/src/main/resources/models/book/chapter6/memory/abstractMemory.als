module chapter6/memory/abstractMemory [Addr, Data] ----- the model from page 217

sig Memory {
	data: Addr -> lone Data
	}

pred init [m: Memory] {
	no m.data
	}

pred write [m, m1: Memory, a: Addr, d: Data] {
	m1.data = m.data ++ a -> d
	}

pred read [m: Memory, a: Addr, d: Data] {
	let d1 = m.data [a] | some d1 implies d = d1
	}

fact Canonicalize {
	no disj m, m1: Memory | m.data = m1.data
	}

// This command should not find any counterexample
WriteRead: check {
	all m, m1: Memory, a: Addr, d1, d2: Data |
		write [m, m1, a, d1] and read [m1, a, d2] => d1 = d2
	}

// This command should not find any counterexample
WriteIdempotent: check {
	all m, m1, m": Memory, a: Addr, d: Data |
		write [m, m1, a, d] and write [m1, m", a, d] => m1 = m"
	}
