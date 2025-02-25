#lang forge/froglet

// sig Order {
//     current : lone Player,
//     next : lone Player
// }

sig Hand {
    fingers : lone Int
}

sig Player {
    hand1 : lone Hand,
    hand2 : lone Hand,
    next: lone Player
}

fun countFingers[p1: Player, p2: Player]: one Int {
    add[p1.hand1.fingers, p1.hand2.fingers, p2.hand1.fingers, p2.hand2.fingers]
}

pred disjointHands {
    all h: Hand | {
        all disj p1, p2: Player | {
            reachable[h, p1, hand1] implies not reachable[h, p2, hand1]
            reachable[h, p1, hand1] implies not reachable[h, p2, hand2]
            reachable[h, p1, hand2] implies not reachable[h, p2, hand1]
            reachable[h, p1, hand2] implies not reachable[h, p2, hand2]

            reachable[h, p1, hand1] implies not reachable[h, p1, hand2]
            reachable[h, p1, hand2] implies not reachable[h, p2, hand1]
        }
    }
}

pred reachableHands {
    all h: Hand | {
        some p: Player {
            reachable[h, p, hand1] or reachable[h, p, hand2]
        }
    }
}

pred reachablePlayers {
    some first: Player | 
        all p: Player | reachable[first, p, next]
}


// pred p1turn[o: Order] {
//     o.current = p1
//     o.next = p2
// } 

// pred p2turn[o: Order] {
//     o.current = p2
//     o.next = p1
// }

// pred valid[o: Order] {
//     p1turn[o] or p2turn[o]
// }

pred winning {
    some p1, p2: Player | {
        p2.next = none
        p1.next = p2
        add[p1.hand1.fingers, p1.hand2.fingers] >= 7
        add[p2.hand1.fingers, p2.hand2.fingers] < 7
    }
}

pred init{
    some p: Player| {
	p.hand1.fingers = 1
    p.hand2.fingers = 1
    }
}

pred move[p1: Player, p2: Player] {
    p1.next = p2
    (countFingers[p1, p1.next] = add[countFingers[p1, p2], p1.hand1.fingers] or
    countFingers[p1, p1.next] = add[countFingers[p1, p2], p1.hand2.fingers])
}

run {
    some p1, p2, p3: Player |
        init // and
        // move[p1, p2] and
        // move[p2, p3]
    disjointHands
    reachablePlayers
    // reachableHands
} for exactly 3 Player, exactly 6 Hand