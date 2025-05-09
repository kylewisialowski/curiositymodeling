
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

test suite for winning {
    // someone loses both hands
    assert someLoser is necessary for winning for exactly 2 Player
    // someone has fingers on at least one hand
    assert someWinner is necessary for winning for exactly 2 Player
}

// no players experience any changes
pred nothingChanges {
    #{p : Player | p.hand1' != p.hand1} = 0
    #{p : Player | p.hand2' != p.hand2} = 0
    #{p : Player | p.turn' != p.turn} = 0
}

test suite for static {
    // nothing changes between moves
    assert nothingChanges is necessary for static for exactly 2 Player
}