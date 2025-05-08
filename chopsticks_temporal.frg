#lang forge/temporal

option max_tracelength 12
option min_tracelength 6

---------- Definitions ----------


sig Player {
<<<<<<< HEAD
    var hand1 : lone Int,
    var hand2 : lone Int,
    var turn : lone Int
}

=======
    hand1 : one Hand,
    hand2 : one Hand,
    var turn : one Int
}

sig Hand {
    var fingers : one Int
}

>>>>>>> e16505e048bbfa7e3c8cd0af5197e9a2b6159bdb
pred validState {
    // fingers between 0 and 5

    // two hands at all times
    all p : Player | {
        one p.hand1 and one p.hand2
    }

<<<<<<< HEAD
=======
    all disj p, p2 : Player | {
        p.hand1 != p2.hand1
        p.hand1 != p2.hand2
        p.hand2 != p2.hand1
        p.hand2 != p2.hand2
        p.hand1 != p.hand2
        p2.hand1 != p2.hand2
    }



>>>>>>> e16505e048bbfa7e3c8cd0af5197e9a2b6159bdb
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

pred validSplit {
    one current: Player | {
        current.turn = 1

        one target: Player | {
            current != target

            // target's hands should NOT change
            target.hand1.fingers' = target.hand1.fingers
            target.hand2.fingers' = target.hand2.fingers

            // total number for current should stay the same
            let new_total = add[current.hand1.fingers', current.hand2.fingers'],
                original_total = add[current.hand1.fingers, current.hand2.fingers] |
                    new_total = original_total
            current.hand1.fingers' != current.hand1.fingers and current.hand2.fingers' != current.hand2.fingers
            current.hand1.fingers' >= 0 and current.hand1.fingers' < 5
            current.hand2.fingers' >= 0 and current.hand2.fingers' < 5

            // Turn switching
            current.turn' = 0
            target.turn' = 1
        }
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
<<<<<<< HEAD
    always validTurn
    eventually winning
} for exactly 2 Player 
=======
    always {validTurn or validSplit}
    //eventually winning
} for exactly 2 Player
>>>>>>> e16505e048bbfa7e3c8cd0af5197e9a2b6159bdb
