module examples/systems/marksweepgc

/*
 * Model of mark and sweep garbage collection.
 */

// a node in the heap
sig Node {}

sig HeapState {
  left, right : Node -> lone Node,
  marked : set Node,
  freeList : lone Node
}

pred clearMarks[hs, hs1 : HeapState] {
  // clear marked set
  no hs1.marked
  // left and right fields are unchanged
  hs1.left = hs.left
  hs1.right = hs.right
}

/**
 * simulate the recursion of the mark() function using transitive closure
 */
fun reachable[hs: HeapState, n: Node] : set Node {
  n + n.^(hs.left + hs.right)
}

pred mark[hs: HeapState, from : Node, hs1: HeapState] {
  hs1.marked = hs.reachable[from]
  hs1.left = hs.left
  hs1.right = hs.right
}

/**
 * complete hack to simulate behavior of code to set freeList
 */
pred setFreeList[hs, hs1: HeapState] {
  // especially hackish
  hs1.freeList.*(hs1.left) in (Node - hs.marked)
  all n: Node |
    (n !in hs.marked) => {
      no hs1.right[n]
      hs1.left[n] in (hs1.freeList.*(hs1.left))
      n in hs1.freeList.*(hs1.left)
    } else {
      hs1.left[n] = hs.left[n]
      hs1.right[n] = hs.right[n]
    }
  hs1.marked = hs.marked
}

pred GC[hs: HeapState, root : Node, hs1: HeapState] {
  some hs1, hs2: HeapState |
    hs.clearMarks[hs1] && hs1.mark[root, hs2] && hs2.setFreeList[hs1]
}

assert Soundness1 {
  all h, h1 : HeapState, root : Node |
    h.GC[root, h1] =>
      (all live : h.reachable[root] | {
        h1.left[live] = h.left[live]
        h1.right[live] = h.right[live]
      })
}

assert Soundness2 {
  all h, h1 : HeapState, root : Node |
    h.GC[root, h1] =>
      no h1.reachable[root] & h1.reachable[h1.freeList]
}

assert Completeness {
  all h, h1 : HeapState, root : Node |
    h.GC[root, h1] =>
      (Node - h1.reachable[root]) in h1.reachable[h1.freeList]
}

check Soundness1 for 3 expect 0
check Soundness2 for 3 expect 0
check Completeness for 3 expect 0
