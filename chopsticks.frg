#lang forge/froglet

// sig Order {
//     current : lone Player,
//     next : lone Player
// }

sig Hand {
    fingers : one Int
}

sig Player {
    hand1 : lone Hand,
    hand2 : lone Hand,
    next: one Player
}

// fun countFingers[p1: Player, p2: Player]: one Int {
//     add[p1.hand1.fingers, p1.hand2.fingers, p2.hand1.fingers, p2.hand2.fingers]
// }

pred disjointHands {
    all h: Hand | {
        all disj p1, p2: Player | {
            reachable[h, p1, hand1] implies not reachable[h, p2, hand1]
            reachable[h, p1, hand1] implies not reachable[h, p2, hand2]
            reachable[h, p1, hand2] implies not reachable[h, p2, hand1]
            reachable[h, p1, hand2] implies not reachable[h, p2, hand2]

            reachable[h, p1, hand1] implies not reachable[h, p1, hand2]
            reachable[h, p2, hand1] implies not reachable[h, p2, hand2]
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
    all p1, p2: Player | reachable[p1, p2, next]
}

pred alwaysTwoHands {
    all p: Player | {
        one p.hand1 and one p.hand2
    }
}

// pred disjointPlayers {
//     all disj p1, p2: Player | {
//         reachable[p1, p2, next] implies not reachable[p2, p1, next]
//     }
// }


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

// pred winning[p1: Player, losingPlayer: Player, winningPlayer: Player] {
//     add[losingPlayer.hand1.fingers, losingPlayer.hand2.fingers] >= 7
//     add[winningPlayer.hand1.fingers, winningPlayer.hand2.fingers] < 7
//     winningPlayer.next = losingPlayer
//     losingPlayer.next = p1
// }

pred winning[p1: Player] {
    some p1, losingPlayer, winningPlayer: Player | {
        add[losingPlayer.hand1.fingers, losingPlayer.hand2.fingers] >= 7
        add[winningPlayer.hand1.fingers, winningPlayer.hand2.fingers] < 7
        winningPlayer.next = losingPlayer
        losingPlayer.next = p1 
    }
}

// pred winning[winner: Player, loser: Player] {
//     add[loser.hand1.fingers, loser.hand2.fingers] >= 7
//     add[winner.hand1.fingers, winner.hand2.fingers] < 7
//     winner.next = loser
//     loser.next = winner
// }

pred init[p1: Player, p2: Player] {
    // temp = p1
    p1.next = p2
    // p2.next = temp

    p1.hand1.fingers = 1
    p1.hand2.fingers = 1
    p2.hand1.fingers = 1
    p2.hand2.fingers = 1
}

pred noNegativeFingers {
    all h: Hand | h.fingers >= 1
}

pred move[p1: Player, p2: Player, p3: Player] {
    // p1.next = p2 -- we already do this in init
    p2.next = p3
    
    add[p3.hand1.fingers, p3.hand2.fingers] = add[p1.hand1.fingers, p1.hand2.fingers, p2.hand1.fingers] or 
    add[p3.hand1.fingers, p3.hand2.fingers] = add[p1.hand1.fingers, p1.hand2.fingers, p2.hand2.fingers]

    -- Hands cannot lose fingers (ensures only valid moves)
    p3.hand1.fingers >= p1.hand1.fingers
    p3.hand2.fingers >= p1.hand2.fingers

    // (countFingers[p1, p1.next] = add[countFingers[p1, p2], p1.hand1.fingers] or
    // countFingers[p1, p1.next] = add[countFingers[p1, p2], p1.hand2.fingers])
}


// run {
//     some p1, p2, temp: Player | {
//         init[p1, p2, temp] // and
//         noNegativeFingers
//         move[p1, p2, p1]
//         // move[p2, p1, p2]
//         // winning[p1, p2] or winning[p2, p1]
//         // disjointHands
//         // reachablePlayers
//         // alwaysTwoHands
//         // reachableHands
//     }
// } for exactly 2 Player, exactly 2 Hand

run {
    some p1, p2, p3, p4, p5, p6: Player | {
        init[p1, p2] // and
        noNegativeFingers
        move[p1, p2, p3]
        move[p2, p3, p4]
        move[p3, p4, p5]
        move[p4, p5, p6]
        winning[p1]
        disjointHands
        reachablePlayers
        alwaysTwoHands
        // disjointPlayers
        reachableHands
    }
} for exactly 6 Player, exactly 12 Hand // will be unsat with less than this, is sat for anything greater