open util/ordering[Time]

sig Time { }

let dynamic[x] = x one-> Time

let dynamicSet[x] = x -> Time

let then [a, b, t, t2] {
    some x:Time | a[t,x] && b[x,t2]
}

let while = while3

let while9 [cond, body, t, t2] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while8[cond,body,x,t2]
}

let while8 [cond, body, t, t2] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while7[cond,body,x,t2]
}

let while7 [cond, body, t, t2] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while6[cond,body,x,t2]
}

let while6 [cond, body, t, t2] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while5[cond,body,x,t2]
}

let while5 [cond, body, t, t2] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while4[cond,body,x,t2]
}

let while4 [cond, body, t, t2] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while3[cond,body,x,t2]
}

let while3 [cond, body, t, t2] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while2[cond,body,x,t2]
}

let while2 [cond, body, t, t2] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while1[cond,body,x,t2]
}

let while1 [cond, body, t, t2] {
    some x:Time | (cond[t] => body[t,x] else t=x) && while0[cond,body,x,t2]
}

let while0 [cond, body, t, t2] {
    !cond[t] && t=t2
}
