
#lang forge/temporal

open "chopsticks_temporal.frg"

// hands have 1 finger
pred oneFinger {
    all p : Player | {
        p.hand1 = 1
        p.hand2 = 1
    }
}

// only one person starts with a turn
pred startTurn {
    #{p : Player | p.turn = 1} = 1
    #{p : Player | p.turn = 1} = subtract[#{p : Player | p.turn = 0 or p.turn = 1}, 1]
}

test suite for initState {
    // all hands start with 1 finger
    assert oneFinger is necessary for initState for exactly 2 Player
    // only one player starts with a turn
    assert startTurn is necessary for initState for exactly 2 Player

    test expect {

        // normal init -- all hands start with 1 finger
        init1 : {
            some p, p2 : Player | {
                p.hand1 = 1
                p.hand2 = 1
                p2.hand1 = 1
                p2.hand2 = 1
                initState
            }
        } is sat

        // bad init (not all starting with 1 finger)
        init2 : {
            one p, p2 : Player | {
                p.hand1 = 1
                p.hand2 = 1
                p2.hand1 = 1
                p2.hand2 = 2
                initState
            }
        } is unsat

        // good init with turns
        init3 : {
            some p, p2 : Player | {
                p.hand1 = 1
                p.hand2 = 1
                p2.hand1 = 1
                p2.hand2 = 1
                p.turn = 0
                p2.turn = 1
                initState
            }
        } is sat

        // bad init with turns (can't both start with a turn)
        init4 : {
            one disj p, p2 : Player | {
                p.hand1 = 1
                p.hand2 = 1
                p2.hand1 = 1
                p2.hand2 = 1
                p.turn = 1
                p2.turn = 1
                initState
            }
        } is unsat
        
    }
}

// player's total fingers during turn = player's total fingers during next turn
pred totalFingers {
    all p : Player {
        add[p.hand1', p.hand2'] = add[p.hand1, p.hand2]
    }
}

// only one player has hands that change
pred oneChange {
    #{p : Player | p.hand1' != p.hand1 and p.hand2' != p.hand2} = 1
    #{p : Player | p.hand1' != p.hand1 or p.hand2' != p.hand2} = 1
}

// all fingers stay within the allowed bounds
pred legalFingers {
    #{p : Player | p.hand1' < 0 or p.hand1' > 5 or p.hand2' < 0 or p.hand2' > 5} = 0
}

test suite for validSplit {
    // all player's must have same number of fingers preserved through the split
    assert totalFingers is necessary for validSplit for exactly 2 Player
    // exactly one player has hands that change number of fingers
    assert oneChange is necessary for validSplit for exactly 2 Player
    // all fingers stay within legal bounds (0 and 5)
    assert legalFingers is necessary for validSplit for exactly 2 Player

    test expect {

        // normal split with one hand going to 0
        split1 : {
            some p : Player {
                p.hand1 = 1
                p.hand2 = 2
                p.hand1' = 0
                p.hand2' = 3
                validSplit
            }
        } is sat

        // fingers only switch hands (this should not happen)
        split2 : {
            some p : Player {
                p.hand1 = 1
                p.hand2 = 2
                p.hand1' = 2
                p.hand2' = 1
                validSplit
            }
        } is unsat

        // proper turn switching
        split3 : {
            some p : Player {
                p.hand1 = 4
                p.hand2 = 2
                p.turn = 1
                p.hand1' = 3
                p.hand2' = 3
                p.turn' = 0
                validSplit
            }
        } is sat

        // validSplit without additional validTurn move (split counts as a turn)
        split4 : {
            some p : Player {
                p.hand1 = 4
                p.hand2 = 2
                p.turn = 1
                p.hand1' = 3
                p.hand2' = 3
                p.turn' = 0
                validSplit
                not validTurn
            }
        } is sat
    }
    
}

// exactly one hand changes during the turn
pred oneChangeTurn {
    #{p : Player | p.hand1' != p.hand1 or p.hand2' != p.hand2} = 1
    all p : Player {
        p.hand1' != p.hand1 implies p.hand2' = p.hand2
        p.hand2' != p.hand2 implies p.hand1' = p.hand1
    }
}

// different possibilities for how a hand can change
pred sumFingers {
    some disj p, p2 : Player | {
        p.hand1' = add[p.hand1, p2.hand1] or
        p.hand1' = add[p.hand1, p2.hand2] or
        p.hand2' = add[p.hand2, p2.hand1] or
        p.hand2' = add[p.hand2, p2.hand2] or
        p.hand1' = 0 or
        p.hand2' = 0
    }
}

// if a hand "overflows," player gets reset to 0 fingers
pred loseHand {

    some disj p, p2 : Player | {
        p.hand1' = 0 implies {
            add[p.hand1, p2.hand1] > 5 or
            add[p.hand1, p2.hand2] > 5 or
            p.hand1 = 0
        }

        p.hand2' = 0 implies {
            add[p.hand2, p2.hand1] > 5 or
            add[p.hand2, p2.hand2] > 5 or
            p.hand2 = 0
        }
    }
}

test suite for validTurn {
    // exactly one hand changes during the turn
    assert oneChangeTurn is necessary for validTurn for exactly 2 Player
    // one of the allowed changes occurs
    assert sumFingers is necessary for validTurn for exactly 2 Player
    // player loses a hand under the appropriate conditions
    assert loseHand is necessary for validTurn for exactly 2 Player
    // legal number of fingers on each hand is preserved
    assert legalFingers is necessary for validTurn for exactly 2 Player

    test expect {

        // normal turn switch (p to p2)
        turn1 : {
                some p, p2 : Player {
                    p.hand1 = 1
                    p.hand2 = 2
                    p.turn = 1
                    p2.hand1 = 1
                    p2.hand2 = 1
                    p2.turn = 0

                    p.hand1' = 1
                    p.hand2' = 2
                    p.turn'= 0
                    p2.hand1' = 1
                    p2.hand2' = 3
                    p2.turn' = 1

                    validTurn
                }
            } is sat

        // turn doesn't change
        turn2 : {
                some p, p2 : Player {
                    p.hand1 = 1
                    p.hand2 = 2
                    p.turn = 1
                    p2.hand1 = 1
                    p2.hand2 = 1
                    p2.turn = 0

                    p.hand1' = 1
                    p.hand2' = 2
                    p.turn'= 1
                    p2.hand1' = 1
                    p2.hand2' = 3
                    p2.turn' = 0

                    validTurn
                }
            } is unsat

        // hands don't change
        turn3 : {
                some p, p2 : Player {
                    p.hand1 = 1
                    p.hand2 = 2
                    p.turn = 1
                    p2.hand1 = 1
                    p2.hand2 = 1
                    p2.turn = 0

                    p.hand1' = 1
                    p.hand2' = 2
                    p.turn'= 0
                    p2.hand1' = 1
                    p2.hand2' = 1
                    p2.turn' = 1

                    validTurn
                }
            } is unsat

        // adding too many fingers
        turn4 : {
                some p, p2 : Player {
                    p.hand1 = 1
                    p.hand2 = 2
                    p.turn = 1
                    p2.hand1 = 1
                    p2.hand2 = 1
                    p2.turn = 0

                    p.hand1' = 1
                    p.hand2' = 2
                    p.turn'= 0
                    p2.hand1' = 1
                    p2.hand2' = 5
                    p2.turn' = 1

                    validTurn
                }
            } is unsat
        
        // good exchange of fingers 
        turn5 : {
                some p, p2 : Player {
                    p.hand1 = 1
                    p.hand2 = 2
                    p.turn = 1
                    p2.hand1 = 1
                    p2.hand2 = 1
                    p2.turn = 0

                    p.hand1' = 1
                    p.hand2' = 2
                    p.turn'= 0
                    p2.hand1' = 1
                    p2.hand2' = 3
                    p2.turn' = 1

                    validTurn
                }
            } is sat
        
        // good exchange of fingers (with overflow)
        turn6 : {
                some p, p2 : Player {
                    p.hand1 = 2
                    p.hand2 = 2
                    p.turn = 1
                    p2.hand1 = 3
                    p2.hand2 = 4
                    p2.turn = 0

                    p.hand1' = 2
                    p.hand2' = 2
                    p.turn'= 0
                    p2.hand1' = 3
                    p2.hand2' = 0
                    p2.turn' = 1

                    validTurn
                }
            } is sat
        
        // good exchange and leads to winning
        turn7 : {
                some p, p2 : Player {
                    p.hand1 = 1
                    p.hand2 = 2
                    p.turn = 1
                    p2.hand1 = 0
                    p2.hand2 = 4
                    p2.turn = 0

                    p.hand1' = 1
                    p.hand2' = 2
                    p.turn'= 0
                    p2.hand1' = 0
                    p2.hand2' = 0
                    p2.turn' = 1

                    (p.hand1')' = 1
                    (p.hand2')' = 1
                    (p.turn')'= 1
                    (p2.hand1')' = 1
                    (p2.hand2')' = 1
                    (p2.turn')' = 0

                    validTurn implies winning
                }
            } is sat
        
        // good exchange / valid move, cannot split in same turn
        turn8 : {
                some p, p2 : Player {
                    p.hand1 = 2
                    p.hand2 = 2
                    p.turn = 1
                    p2.hand1 = 3
                    p2.hand2 = 4
                    p2.turn = 0

                    p.hand1' = 2
                    p.hand2' = 2
                    p.turn'= 0
                    p2.hand1' = 3
                    p2.hand2' = 0
                    p2.turn' = 1

                    validTurn
                    not validSplit
                }
            } is sat
    }
}

// someone must lose both hands
pred someLoser {
    some p : Player | {
        p.hand1 = 0 and p.hand2 = 0
    }
}

// someone must retain fingers on at least one hand
pred someWinner {
    some p : Player | {
        p.hand1 > 0 or p.hand2 > 0
    }
}

// all hands revert to 1 finger
pred allOne {
    all p : Player | {
        p.hand1' = 1 and p.hand2' = 1
    }
}

test suite for winning {
    // someone loses both hands
    assert someLoser is necessary for winning for exactly 2 Player
    // someone has fingers on at least one hand
    assert someWinner is necessary for winning for exactly 2 Player
    // make sure we loop back to init configuation
    assert allOne is necessary for winning for exactly 2 Player

    test expect {

        // normal winning conditions (one living hand) + good reset
        win1 : {
            some p, p2 : Player {
                p.hand1 = 1
                p.hand2 = 0
                p2.hand1 = 0
                p2.hand2 = 0

                p.hand1' = 1
                p.hand2' = 1
                p2.hand1' = 1
                p.hand2' = 1
                p.turn' = 1
                p2.turn' = 0

                winning
            }
        } is sat

        // bad reset (all next hands should go to 1 finger)
        win2 : {
            some p, p2 : Player {
                p.hand1 = 0
                p.hand2 = 0
                p2.hand1 = 0
                p2.hand2 = 0

                p.hand1' = 1
                p.hand2' = 1
                p2.hand1' = 1
                p.hand2' = 0
                p.turn' = 1
                p2.turn' = 0

                winning
            }
        } is unsat

        // good winning conditions (two living hands) + good reset
        win3 : {
            some p, p2 : Player {
                p.hand1 = 1
                p.hand2 = 3
                p2.hand1 = 0
                p2.hand2 = 0

                p.hand1' = 1
                p.hand2' = 1
                p2.hand1' = 1
                p.hand2' = 1
                p.turn' = 1
                p2.turn' = 0

                winning
            }
        } is sat
    }
}
