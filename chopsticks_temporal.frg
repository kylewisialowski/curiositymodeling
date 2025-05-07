#lang forge/temporal

option max_tracelength 20
option min_tracelength 2

---------- Definitions ----------

sig Player {
    hand1 : one Hand,
    hand2 : one Hand,
    var turn : one Int
}

sig Hand {
    var fingers : one Int
}

pred validState {

    // fingers between 0 and 5
    // all h : Hand | {
    //     h.fingers >= 0
    //     // h.fingers < 5
    // }

    // two hands at all times
    all p : Player | {
        p.turn = 0 or p.turn = 1
    }
    
    // All players have their own hand
    all disj p, p2 : Player | {
        p.hand1 != p2.hand1
        p.hand1 != p2.hand2
        p.hand2 != p2.hand2
        p.hand1 != p.hand2
    }

    // Exactly one player has turn=1
    #{p: Player | p.turn = 1} = 1

    all p : Player | {
        p.turn = 0 or p.turn = 1
    }
}

pred initState {    
    all p : Player | {
        p.hand1.fingers = 1
        p.hand2.fingers = 1
        p.turn = 0 or p.turn = 1
    }
    one p : Player | p.turn = 1
}


pred addToHand[current : Player, target : Player] {
    target.hand1.fingers' < 5 and target.hand2.fingers' < 5

    target.hand1.fingers' != target.hand1.fingers implies {
        (target.hand1.fingers' = add[target.hand1.fingers, current.hand1.fingers] or 
        target.hand1.fingers' = add[target.hand1.fingers, current.hand2.fingers])
    }

    target.hand2.fingers' != target.hand2.fingers implies {
        (target.hand2.fingers' = add[target.hand2.fingers, current.hand1.fingers] or 
        target.hand2.fingers' = add[target.hand2.fingers, current.hand2.fingers])
    }

}

pred loseHand[current : Player, target : Player] {
    target.hand1.fingers' = 0 or target.hand2.fingers' = 0

    target.hand1.fingers' = 0 implies {
        add[target.hand1.fingers, current.hand1.fingers] >= 5 or
        add[target.hand1.fingers, current.hand2.fingers] >= 5
    }

    target.hand2.fingers' = 0 implies {
        add[target.hand2.fingers, current.hand1.fingers] >= 5 or
        add[target.hand2.fingers, current.hand2.fingers] >= 5
    }
}

pred validTurn {
    // Player whose turn it is
    one current: Player | {
        current.turn = 1

        // Find exactly one target to attack
        one target: Player | {
            target != current 

            (target.hand1.fingers' != target.hand1.fingers or
            target.hand2.fingers' != target.hand2.fingers)

            #{h : Hand | h.fingers' != h.fingers} = 1

            addToHand[current, target] or loseHand[current, target]
                      
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
    always validState
    always validTurn
    eventually winning
} for exactly 2 Player