
#lang forge/temporal

open "chopsticks_temporal.frg"

pred oneFinger {
    all p : Player | {
        p.hand1 = 1
        p.hand2 = 1
    }
}

pred startTurn {
    #{p : Player | p.turn = 1} = 1
    #{p : Player | p.turn = 1} = subtract[#{p : Player | p.turn = 0 or p.turn = 1}, 1]
}

test suite for initState {
    assert oneFinger is necessary for initState for exactly 2 Player
    assert startTurn is necessary for initState for exactly 2 Player
}

pred totalFingers {
    all p : Player {
        add[p.hand1', p.hand2'] = add[p.hand1, p.hand2]
    }
}

pred oneChange {
    #{p : Player | p.hand1' != p.hand1 and p.hand2' != p.hand2} = 1
    #{p : Player | p.hand1' != p.hand1 or p.hand2' != p.hand2} = 1
}

pred legalFingers {
    #{p : Player | p.hand1' < 0 or p.hand1' > 5 or p.hand2' < 0 or p.hand2' > 5} = 0
}

test suite for validSplit {
    assert totalFingers is necessary for validSplit for exactly 2 Player
    assert oneChange is necessary for validSplit for exactly 2 Player
    assert legalFingers is necessary for validSplit for exactly 2 Player
}

pred oneChangeTurn {
    #{p : Player | p.hand1' != p.hand1 or p.hand2' != p.hand2} = 1
    all p : Player {
        p.hand1' != p.hand1 implies p.hand2' = p.hand2
        p.hand2' != p.hand2 implies p.hand1' = p.hand1
    }
}

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
    assert oneChangeTurn is necessary for validTurn for exactly 2 Player
    assert sumFingers is necessary for validTurn for exactly 2 Player
    assert loseHand is necessary for validTurn for exactly 2 Player
    assert legalFingers is necessary for validTurn for exactly 2 Player
}
