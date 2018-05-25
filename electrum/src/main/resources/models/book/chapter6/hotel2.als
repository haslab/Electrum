module chapter6/hotel2 --- the final model in Fig 6.7

open util/ordering[Time] as to
open util/ordering[Key] as ko

sig Key {}
sig Time {}

sig Room {
	keys: set Key,
	currentKey: keys one -> Time
	}

fact DisjointKeySets {
	-- each key belongs to at most one room
	Room<:keys   in   Room lone-> Key
	}

one sig FrontDesk {
	lastKey: (Room -> lone Key) -> Time,
	occupant: (Room -> Guest) -> Time
	}

sig Guest {
	keys: Key -> Time
	}

fun nextKey [k: Key, ks: set Key]: set Key {
	min [k.nexts & ks]
	}

pred init [t: Time] {
	no Guest.keys.t
	no FrontDesk.occupant.t
	all r: Room | FrontDesk.lastKey.t [r] = r.currentKey.t
	}

pred entry [t, t1: Time, g: Guest, r: Room, k: Key] {
	k in g.keys.t
	let ck = r.currentKey |
		(k = ck.t and ck.t1 = ck.t) or 
		(k = nextKey[ck.t, r.keys] and ck.t1 = k)
	noRoomChangeExcept [t, t1, r]
	noGuestChangeExcept [t, t1, none]
	noFrontDeskChange [t, t1]
	}

pred noFrontDeskChange [t, t1: Time] {
	FrontDesk.lastKey.t = FrontDesk.lastKey.t1
	FrontDesk.occupant.t = FrontDesk.occupant.t1
	}

pred noRoomChangeExcept [t, t1: Time, rs: set Room] {
	all r: Room - rs | r.currentKey.t = r.currentKey.t1
	}
	
pred noGuestChangeExcept [t, t1: Time, gs: set Guest] {
	all g: Guest - gs | g.keys.t = g.keys.t1
	}

pred checkout [t, t1: Time, g: Guest] {
	let occ = FrontDesk.occupant {
		some occ.t.g
		occ.t1 = occ.t - Room ->g
		}
	FrontDesk.lastKey.t = FrontDesk.lastKey.t1
	noRoomChangeExcept [t, t1, none]
	noGuestChangeExcept [t, t1, none]
	}

pred checkin [t, t1: Time, g: Guest, r: Room, k: Key] {
	g.keys.t1 = g.keys.t + k
	let occ = FrontDesk.occupant {
		no occ.t [r]
		occ.t1 = occ.t + r -> g
		}
	let lk = FrontDesk.lastKey {
		lk.t1 = lk.t ++ r -> k
		k = nextKey [lk.t [r], r.keys]
		}
	noRoomChangeExcept [t, t1, none]
	noGuestChangeExcept [t, t1, g]
	}

fact traces {
	init [first]
	all t: Time-last | let t1 = t.next |
		some g: Guest, r: Room, k: Key |
			entry [t, t1, g, r, k]
			or checkin [t, t1, g, r, k]
			or checkout [t, t1, g]
	}

fact NoIntervening {
	all t: Time-last | let t1 = t.next, t" = t1.next |
		all g: Guest, r: Room, k: Key |
			checkin [t, t1, g, r, k] => (entry [t1, t", g, r, k] or no t")
	}

assert NoBadEntry {
	all t: Time, r: Room, g: Guest, k: Key |
		let t1 = t.next, o = FrontDesk.occupant.t[r] | 
			entry [t, t1, g, r, k] and some o => g in o
	}

// After adding the NoIntervening fact,
// these commands no longer generate counterexamples
check NoBadEntry for 3 but 2 Room, 2 Guest, 5 Time
check NoBadEntry for 3 but 3 Room, 3 Guest, 7 Time
check NoBadEntry for 5 but 3 Room, 3 Guest, 9 Time
