module hotel

open util/ordering [Time] as timeOrder

sig Key, Time {}

sig Card {
	fst, snd: Key
	}

sig Room {
	key: Key one->Time
	}

one sig Desk {
	issued: Key->Time,
	prev: (Room->lone Key)->Time
	}

sig Guest {
	cards: Card->Time
	}

pred init [t: Time] {
	Desk.prev.t = key.t
	no issued.t and no cards.t ------ bug! (see page 303)
	}

pred checkin [t,t1: Time, r: Room, g: Guest] {
	some c: Card {
		c.fst = r.(Desk.prev.t)
		c.snd not in Desk.issued.t
		cards.t1 = cards.t + g->c ------------- bug! (see page 306)
		Desk.issued.t1 = Desk.issued.t + c.snd
		Desk.prev.t1 = Desk.prev.t ++ r->c.snd
		}
	key.t = key.t1
	}

pred enter [t,t1: Time, r: Room, g: Guest] {
	some c: g.cards.t |
		let k = r.key.t {
			c.snd = k and key.t1 = key.t
			or c.fst = k and key.t1 = key.t ++ r->c.snd
			}
	issued.t = issued.t1 and (Desk<:prev).t = prev.t1
	cards.t = cards.t1
	}

fact Traces {
	init [first]
	all t: Time - last | some g: Guest, r: Room |
		checkin [t, t.next, r, g] or enter[t, t.next, r, g]
	}

assert NoIntruder {
	no t1: Time, g: Guest, g1: Guest-g, r: Room |
		let t2=t1.next, t3=t2.next, t4=t3.next {
			enter [t1, t2, r, g]
			enter [t2, t3, r, g1]
			enter [t3, t4, r, g]
		}
	}

-- This check reveals a bug (similar to Fig E.3) in which the initial key was issued twice.
check NoIntruder for 3 but 6 Time, 1 Room, 2 Guest
