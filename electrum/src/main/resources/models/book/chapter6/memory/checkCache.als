module chapter6/memory/checkCache [Addr, Data]

open chapter6/memory/cacheMemory [Addr, Data] as cache
open chapter6/memory/abstractMemory [Addr, Data] as amemory

fun alpha [c: CacheSystem]: Memory {
	{m: Memory | m.data = c.main ++ c.cache}
	}

// This check should not produce a counterexample
ReadOK: check {
	// introduction of m, m1 ensures that they exist, and gives witnesses if counterexample
	all c: CacheSystem, a: Addr, d: Data, m: Memory |
		cache/read [c, a, d] and m = alpha [c] => amemory/read [m, a, d]
	}

// This check should not produce a counterexample
WriteOK: check {
	all c, c1: CacheSystem, a: Addr, d: Data, m, m1: Memory |
		cache/write [c, c1, a, d] and m = alpha [c] and m1 = alpha [c1]
 			=> amemory/write [m, m1, a, d]
	}

// This check should not produce a counterexample
LoadOK: check {
	all c, c1: CacheSystem, m, m1: Memory |
		cache/load [c, c1] and m = alpha [c] and m1 = alpha [c1] => m = m1
	}

// This check should not produce a counterexample
FlushOK: check {
	all c, c1: CacheSystem, m, m1: Memory |
		cache/flush [c, c1] and m = alpha [c] and m1 = alpha [c1] => m = m1
	}
