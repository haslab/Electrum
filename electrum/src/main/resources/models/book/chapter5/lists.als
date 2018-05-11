module chapter5/lists ---- page 157

some sig Element {}

abstract sig List {}
one sig EmptyList extends List {}
sig NonEmptyList extends List {
	element: Element,
	rest: List
	}

fact ListGenerator {
	all list: List, e: Element |
		some list1: List | list1.rest = list and list1.element = e
	}

assert FalseAssertion {
	all list: List | list != list
	}

// This check finds no counterexample since
// the only possible counterexamples are infinite.
check FalseAssertion
