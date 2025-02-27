#lang forge/froglet

/*
    This sig defines a Hand. It has one field, 'fingers', which is represented by an integer.
*/
sig Hand {
    fingers : one Int
}

/*
    This sig defines a Player. It has three fields:
    - 'hand1': The Player's left hand, represented by a Hand sig. There can be at most 1 hand1.
    - 'hand2': The Player's right hand, represented by a Hand sig. There can be at most 1 hand2.
    - 'next': The Player that follows the current player.
*/
sig Player {
    hand1 : lone Hand,
    hand2 : lone Hand,
    next: one Player
}

/*
    This predicate checks at all hands in the game are represented as distinct objects from each other.
*/
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

/*
    This predicate checks that all hands are linked to a player in the game.
*/
pred reachableHands {
    all h: Hand | {
        some p: Player {
            reachable[h, p, hand1] or reachable[h, p, hand2]
        }
    }
}

/*
    This predicate checks that all players take turns one after the other.
*/
pred reachablePlayers {
    all p1, p2: Player | reachable[p1, p2, next]
}

/*
    This predicate checks that a player has two hands at any given time.
*/
pred alwaysTwoHands {
    all p: Player | {
        one p.hand1 and one p.hand2
    }
}

/*
    This predicate determines the winning condition for the game.
*/
pred winning[p1: Player, losingPlayer: Player, winningPlayer: Player] {
    add[losingPlayer.hand1.fingers, losingPlayer.hand2.fingers] >= 7
    add[winningPlayer.hand1.fingers, winningPlayer.hand2.fingers] < 7
    winningPlayer.next = losingPlayer
    losingPlayer.next = p1
}

/*
    This predicate determines the starting condition of the game.
*/
pred init[p1: Player, p2: Player] {
    p1.next = p2

    p1.hand1.fingers = 1
    p1.hand2.fingers = 1
    p2.hand1.fingers = 1
    p2.hand2.fingers = 1
}

/*
    This predicate checks that all fingers are represented by positive numbers.
*/
pred noNegativeFingers {
    all h: Hand | h.fingers >= 1
}

/*
    This predicate defines a valid move in the game.
*/
pred move[p1: Player, p2: Player, p3: Player] {
    p2.next = p3
    
    add[p3.hand1.fingers, p3.hand2.fingers] = add[p1.hand1.fingers, p1.hand2.fingers, p2.hand1.fingers] or 
    add[p3.hand1.fingers, p3.hand2.fingers] = add[p1.hand1.fingers, p1.hand2.fingers, p2.hand2.fingers]

    -- Hands cannot lose fingers (ensures only valid moves)
    p3.hand1.fingers >= p1.hand1.fingers
    p3.hand2.fingers >= p1.hand2.fingers
}

run {
    some p1, p2, p3, p4, p5, p6: Player | {
        init[p1, p2] 
        noNegativeFingers
        move[p1, p2, p3]
        move[p2, p3, p4]
        move[p3, p4, p5]
        move[p4, p5, p6]
        winning[p1, p6, p5]
        disjointHands
        reachablePlayers
        alwaysTwoHands
        reachableHands
    } // will be unsat with less than this, is sat for anything greater
} for exactly 6 Player, exactly 12 Hand 