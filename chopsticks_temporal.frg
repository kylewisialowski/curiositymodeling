#lang forge/temporal

option max_tracelength 20
option min_tracelength 10

---------- Definitions ----------

sig Player {
    hand1 : one Hand,
    hand2 : one Hand,
    var turn : one Int
}


sig Hand {
    var fingers : one Int
}

sig Test {
    t : one Int
}

pred what {
    some random : Test | {
        random.t = add[5, 3]
    }
}

pred initState { 

    all p : Player | {
        p.hand1.fingers = 1
        p.hand2.fingers = 1
        p.turn = 0 or p.turn = 1
    }

    one p : Player | p.turn = 1

    // All players have their own hand
    all disj p, p2 : Player | {
        p.hand1 != p2.hand1
        p.hand1 != p2.hand2
        p.hand2 != p2.hand2
        p.hand1 != p.hand2
    }
}

pred addToHand[current : Player, target : Player, ch: Hand, th: Hand] {

    add[ch.fingers, th.fingers] >= 6 implies {
        th.fingers' = 0 or th.fingers' = 0
    }

    add[ch.fingers, th.fingers] < 6 implies {
        th.fingers' = add[ch.fingers, th.fingers] or th.fingers' = add[ch.fingers, th.fingers]
    }

}

pred validTurn {
    // Player whose turn it is
    some current: Player | {
        current.turn = 1

        // Find exactly one target to attack
        some target: Player | {
            target != current 

            #{h : Hand | h.fingers' != h.fingers} = 1

            current.hand1.fingers' = current.hand1.fingers
            current.hand2.fingers' = current.hand2.fingers

            (addToHand[current, target, current.hand1, target.hand1] or
            addToHand[current, target, current.hand1, target.hand2] or
            addToHand[current, target, current.hand2, target.hand1] or
            addToHand[current, target, current.hand2, target.hand2])
                      
            // Turn switching
            current.turn' = 0
            target.turn' = 1
            
        }
    }
}


pred winning {
    some disj p, p2: Player | {
        (p.hand1.fingers = 0 and p.hand2.fingers = 0) and
        (p2.hand1.fingers > 0 or p2.hand2.fingers > 0)
    }
}

run {
    initState
    always validTurn
    eventually winning
    always what
} for exactly 2 Player for {#Int = 5}




// pred loseHand[current : Player, target : Player] {

//     target.hand1.fingers' != target.hand1.fingers implies {
//         ((target.hand1.fingers' = 0) and (add[target.hand1.fingers, current.hand1.fingers] > 5)) or
//         ((target.hand1.fingers' = 0) and (add[target.hand1.fingers, current.hand2.fingers] > 5))
//     }

//     target.hand2.fingers' != target.hand2.fingers  implies {
//         ((target.hand2.fingers' = 0) and (add[target.hand2.fingers, current.hand1.fingers] > 5)) or
//         ((target.hand2.fingers' = 0) and (add[target.hand2.fingers, current.hand2.fingers] > 5))
//     }
// }