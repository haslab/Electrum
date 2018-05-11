module chapter6/memory/fixedSizeMemory_H [Addr, Data]

open chapter6/memory/fixedSizeMemory [Addr, Data] as memory

sig Memory_H extends memory/Memory {
	unwritten: set Addr
	}

pred init [m: Memory_H] {
	memory/init [m]
	m.unwritten = Addr
	}

pred read [m: Memory_H, a: Addr, d: Data] {
	memory/read [m, a, d]
	}

pred write [m, m1: Memory_H, a: Addr, d: Data] {
	memory/write [m, m1, a, d]
	m1.unwritten = m.unwritten - a
	}
