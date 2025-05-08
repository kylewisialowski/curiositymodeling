#lang forge/temporal

option max_tracelength 12
option min_tracelength 6

---------- Definitions ----------


sig Player {
    var hand1 : lone Int,
    var hand2 : lone Int,
    var turn : lone Int
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
        p.hand1 = 1
        p.hand2 = 1
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
            (target.hand1' != target.hand1 and target.hand2' = target.hand2) or
            (target.hand2' != target.hand2 and target.hand1' = target.hand1)
            
            // Apply modulo 5 (hand becomes 0 if sum ≥5)
            target.hand1'!= target.hand1 and target.hand1 != 0 implies {
                let sum1 = add[target.hand1, current.hand1],
                    sum2 = add[target.hand1, current.hand2] |
                        (target.hand1' = sum1 and sum1 < 6) or
                        (target.hand1' = sum2 and sum2 < 6) or
                        (target.hand1' = 0 and (sum1 >= 6 or sum2 >= 6 or sum1 <= 0 or sum2 <= 0))
            }

            target.hand2'!= target.hand2 and target.hand2 != 0 implies {
                let sum1 = add[target.hand2, current.hand1],
                    sum2 = add[target.hand2, current.hand2] |
                        (target.hand2' = sum1 and sum1 < 6) or
                        (target.hand2' = sum2 and sum2 < 6) or
                        (target.hand2' = 0 and (sum1 >= 6 or sum2 >= 6 or sum1 <= 0 or sum2 <= 0))
            }    
            
            // Current player's hands don't change
            current.hand1' = current.hand1
            current.hand2' = current.hand2
            
            // Turn switching
            current.turn' = 0
            target.turn' = 1
            
            // All other players remain unchanged
            all p: Player | p != current and p != target implies {
                p.hand1' = p.hand1
                p.hand2' = p.hand2
                p.turn' = p.turn
            }
        }
    }
}

pred winning {
    some disj p, p2: Player | {
        (p.hand1 = 0 and p.hand2 = 0) and
        (p2.hand1 > 0 or p2.hand2 > 0)
    }
}

run {
    initState
    always validState
    always validTurn
    eventually winning
} for exactly 2 Player 