#lang forge/temporal

option max_tracelength 12
option min_tracelength 5

---------- Definitions ----------

#lang forge/temporal

option max_tracelength 12
option min_tracelength 5

---------- Definitions ----------

sig Player {
    hand1 : lone Hand,
    hand2 : lone Hand,
    var turn : lone Int
}

sig Hand {
    var fingers : lone Int
}

pred validState {
    // fingers between 0 and 5

    // two hands at all times
    all p : Player | {
        one p.hand1 and one p.hand2
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

pred validTurn {
    // Player whose turn it is
    one current: Player | {
        current.turn = 1
        // Find exactly one target to attack
        one target: Player | {
            target != current 
            // Only one of target's hands changes
            (target.hand1.fingers' != target.hand1.fingers and target.hand2.fingers' = target.hand2.fingers) or
            (target.hand2.fingers' != target.hand2.fingers and target.hand1.fingers' = target.hand1.fingers)
            
            // Apply modulo 5 (hand becomes 0 if sum ≥5)
            target.hand1.fingers'!= target.hand1.fingers implies {
                let sum1 = add[target.hand1.fingers, current.hand1.fingers],
                    sum2 = add[target.hand1, current.hand2] |
                        (target.hand1.fingers' = sum1 and sum1 < 5) or
                        (target.hand1.fingers' = sum2 and sum2 < 5) or
                        (target.hand1.fingers' = 0 and (sum1 >= 5 or sum2 >= 5 or sum1 <= 0 or sum2 <= 0))
            }

            target.hand2.fingers'!= target.hand2.fingers implies {
                let sum1 = add[target.hand2.fingers, current.hand1.fingers],
                    sum2 = add[target.hand2.fingers, current.hand2.fingers] |
                        (target.hand2.fingers' = sum1 and sum1 < 5) or
                        (target.hand2.fingers' = sum2 and sum2 < 5) or
                        (target.hand2.fingers' = 0 and (sum1 >= 5 or sum2 >= 5 or sum1 <= 0 or sum2 <= 0))
            }    
            
            // Current player's hands don't change
            current.hand1.fingers' = current.hand1.fingers
            current.hand2.fingers' = current.hand2.fingers
            
            // Turn switching
            current.turn' = 0
            target.turn' = 1
            
            // All other players remain unchanged
            all p: Player | p != current and p != target implies {
                p.hand1.fingers' = p.hand1.fingers
                p.hand2.fingers' = p.hand2.fingers
                p.turn' = p.turn
            }
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
    //eventually winning
} for exactly 2 Player