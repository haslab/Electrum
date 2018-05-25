module chapter6/memory/cacheMemory [Addr, Data] ----- the model from page 219

sig CacheSystem {
	main, cache: Addr -> lone Data
	}

pred init [c: CacheSystem] {
	no c.main + c.cache
	}

pred write [c, c1: CacheSystem, a: Addr, d: Data] {
	c1.main = c.main
	c1.cache = c.cache ++ a -> d
	}

pred read [c: CacheSystem, a: Addr, d: Data] {
	some d
	d = c.cache [a]
	}

pred load [c, c1: CacheSystem] {
	some addrs: set c.main.Data - c.cache.Data |
		c1.cache = c.cache ++ addrs <: c.main
	c1.main = c.main
	}

pred flush [c, c1: CacheSystem] {
	some addrs: some c.cache.Data {
		c1.main = c.main ++ addrs <: c.cache
		c1.cache = c.cache - addrs -> Data
		}
	}

// This command should not find any counterexample
LoadNotObservable: check {
	all c, c1, c": CacheSystem, a1, a2: Addr, d1, d2, d3: Data |
		{
		read [c, a2, d2]
		write [c, c1, a1, d1]
		load [c1, c"]
		read [c", a2, d3]
		} implies d3 = (a1=a2 => d1 else d2)
	}
