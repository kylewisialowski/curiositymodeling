#lang forge/temporal

option max_tracelength 20
option min_tracelength 10

---------- Definitions ----------

sig Player {
    var hand1 : lone Int,
    var hand2 : lone Int,
    var turn : lone Int
}

pred initState {    
    all p : Player | {
        p.hand1 = 1
        p.hand2 = 1
        p.turn = 0 or p.turn = 1
    }
    one p : Player | p.turn = 1
}

pred twoHands {
    all p : Player | {
        some p.hand1
        some p.hand2
    }
}

pred validSplit {

    one current: Player | {
        current.turn = 1

        one target: Player | {
            current != target

            // target's hands should NOT change
            target.hand1' = target.hand1
            target.hand2' = target.hand2

            // total number for current should stay the same
            let new_total = add[current.hand1', current.hand2'],
                original_total = add[current.hand1, current.hand2] |
                    new_total = original_total

            current.hand1' != current.hand1 and current.hand2' != current.hand2
            not (current.hand1' = current.hand2 and current.hand2' = current.hand1)
            current.hand1' >= 0 and current.hand1' <= 5
            current.hand2' >= 0 and current.hand2' <= 5

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

    all p : Player | {
        p.hand1 >= 0
        p.hand2 >= 0
        p.hand1 <= 5
        p.hand2 <= 5
    }

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
            ((target.hand1'!= target.hand1 and target.hand1 != 0 and {
                let sum1 = add[target.hand1, current.hand1],
                    sum2 = add[target.hand1, current.hand2] |
                        (target.hand1' = sum1 and sum1 < 6 and sum1 >= 0) or
                        (target.hand1' = sum2 and sum2 < 6 and sum2 >= 0) or
                        (target.hand1' = 0 and (sum1 >= 6 or sum2 >= 6 or sum1 <= 0 or sum2 <= 0))
            }) or

            (target.hand2'!= target.hand2 and target.hand2 != 0 and {
                let sum1 = add[target.hand2, current.hand1],
                    sum2 = add[target.hand2, current.hand2] |
                        (target.hand2' = sum1 and sum1 < 6 and sum1 >= 0) or
                        (target.hand2' = sum2 and sum2 < 6 and sum2 >= 0) or
                        (target.hand2' = 0 and (sum1 >= 6 or sum2 >= 6 or sum1 <= 0 or sum2 <= 0))
            })) 
            
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

    all p : Player | {
        p.hand1 >= 0
        p.hand2 >= 0
        p.hand1 <= 5
        p.hand2 <= 5
    }

}

pred winning {
    some disj p, p2: Player | {
        (p.hand1 = 0 and p.hand2 = 0) and
        (p2.hand1 > 0 or p2.hand2 > 0)
        p.hand1' = 1
        p.hand2' = 1
        p2.hand1' = 1
        p2.hand2' = 1
    }
}

run {
    initState
    always twoHands
    always (not winning implies (validTurn or validSplit))
    eventually winning
} for exactly 2 Player for {#Int = 5}
