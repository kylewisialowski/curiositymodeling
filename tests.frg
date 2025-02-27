#lang forge/froglet

open "chopsticks.frg"

test suite for disjointHands {
    example validDisjointHands is {disjointHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2
    }

    example overlapDiffPlayersH1toH1 is {not disjointHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h2
        hand1 = `p1 -> `p1h1 + `p2 -> `p1h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2 // p1h1 should not be Player2's h1
    }

    example overlapDiffPlayersH1toH2 is {not disjointHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h1
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p1h1 // p1h1 should not be Player 2's hand2
    }

    example overlapDiffPlayersH2toH1 is {not disjointHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h2
        hand1 = `p1 -> `p1h1 + `p2 -> `p1h2 // p1h2 should not be Player 2's hand1
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2 
    }

    example overlapDiffPlayersH2toH2 is {not disjointHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h1 
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p1h2 // p1h2 should not be Player 2's hand2
    }

    example overlapSamePlayer is {not disjointHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p2h1 + `p2h2
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1 
        hand2 = `p1 -> `p1h1 + `p2 -> `p2h2 // p1h1 should not be Player 1's hand2
    }

    example overlapSamePlayer1 is {not disjointHands} for {
        Player = `p1 + `p2
        Hand = `p1h1 + `p1h2 + `p2h1
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1 
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h1 // p2h1 should not be Player 2's hand 2
    }
}

test suite for reachableHands {
    example canReachHands is {reachableHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2
    }

    example oneLoneHand is {not reachableHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1
        hand2 = `p1 -> `p1h2 
    }

    example allLoneHands is {not reachableHands} for {
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2
    }
}

test suite for reachablePlayers {
    example canReachPlayers is {reachablePlayers} for {
        Player = `p1 + `p2
        next = `p1 -> `p2 + `p2 -> `p1
    }

    example cannotReachPlayers is {not reachablePlayers} for {
        Player = `p1 + `p2
    }

    example multiplePlayers is {reachablePlayers} for {
        Player = `p1 + `p2 + `p3 + `p4
        next = `p1 -> `p2 + `p2 -> `p3 + `p3 -> `p4 + `p4 -> `p1
    }
}

test suite for alwaysTwoHands {
    example twoHands is {alwaysTwoHands} for {
        Player = `p1
        Hand = `p1h1 + `p1h2
        hand1 = `p1 -> `p1h1
        hand2 = `p1 -> `p1h2
    }

    example oneHand is {not alwaysTwoHands} for {
        Player = `p1
        Hand = `p1h1 + `p1h2
        hand1 = `p1 -> `p1h1
    }

    example noHands is {not alwaysTwoHands} for {
        Player = `p1
        Hand = `p1h1 + `p1h2
    }
}

test suite for winning {
    example validWinner is {some p1: Player | winning[p1]} for {
        Player = `p1 + `loser + `winner
        Hand = `loserH1 + `loserH2 + `winnerH1 + `winnerH2
        next = `winner -> `loser + `loser -> `p1 + `p1 -> `winner

        hand1 = `loser -> `loserH1 + `winner -> `winnerH1
        hand2 = `loser -> `loserH2 + `winner -> `winnerH2

        `loserH1.fingers = 3
        `loserH2.fingers = 4
        `winnerH1.fingers = 1
        `winnerH2.fingers = 2
    }

    example noWinner is {no p1: Player | winning[p1]} for {
        Player = `p1 + `p2 + `p3
        Hand = `p2h1 + `p2h2 + `p3h1 + `p3h2

        hand1 = `p2 -> `p2h1 + `p3 -> `p3h1
        hand2 = `p2 -> `p2h2 + `p3 -> `p3h2

        `p2h1.fingers = 2
        `p2h2.fingers = 4
        `p3h1.fingers = 1
        `p3h2.fingers = 2
    }

}

test suite for init {
    example validInit is {all disj p1, p2 : Player | init[p1, p2]} for {
        Player = `p1 + `p2
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2 

        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1 
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2 
        next = `p1 -> `p2 + `p2 -> `p1

        fingers = `p1h1 -> 1 + `p1h2 -> 1 + `p2h1 -> 1 + `p2h2 -> 1
    }

    example initNotOne is {no p1, p2 : Player | init[p1, p2]} for {
        Player = `p1 + `p2
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2 

        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1 
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2 
        next = `p1 -> `p2 + `p2 -> `p1

        fingers = `p1h1 -> 1 + `p1h2 -> 3 + `p2h1 -> 1 + `p2h2 -> 2
    }

}

test suite for noNegativeFingers {
    example positiveFingers is {noNegativeFingers} for {
        Hand = `h
        `h.fingers = 1
    }

    example negativeFingers is {not noNegativeFingers} for {
        Hand = `h
        `h.fingers = -1
    }
    
    // 0 fingers not necessarily negative but is not allowed either
    example zeroFingers is {not noNegativeFingers} for {
        Hand = `h
        `h.fingers = 0
    }
}

test suite for move {
    example validMove is {some p1, p2, p3 : Player | move[p1, p2, p3]} for {
        Player = `p1 + `p2 + `p3
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2 + `p3h1 + `p3h2

        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1 + `p3 -> `p3h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2 + `p3 -> `p3h2
        next = `p1 -> `p2 + `p2 -> `p3 + `p3 -> `p1

        `p1h1.fingers = 1
        `p1h2.fingers = 1
        `p2h1.fingers = 2 // add from p2h1
        `p2h2.fingers = 1
        `p3h1.fingers = 3
        `p3h2.fingers = 1
    }

    example validMove2 is {some p1, p2, p3 : Player | move[p1, p2, p3]} for {
        Player = `p1 + `p2 + `p3
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2 + `p3h1 + `p3h2

        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1 + `p3 -> `p3h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2 + `p3 -> `p3h2
        next = `p1 -> `p2 + `p2 -> `p3 + `p3 -> `p1

        `p1h1.fingers = 1
        `p1h2.fingers = 1
        `p2h1.fingers = 1 
        `p2h2.fingers = 2 // add from p2h2
        `p3h1.fingers = 3
        `p3h2.fingers = 1
    }

    // invalid move
    example addWrongNumber is {no p1, p2, p3 : Player | move[p1, p2, p3]} for {
        Player = `p1 + `p2 + `p3
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2 + `p3h1 + `p3h2

        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1 + `p3 -> `p3h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2 + `p3 -> `p3h2
        next = `p1 -> `p2 + `p2 -> `p3 + `p3 -> `p1

        `p1h1.fingers = 1
        `p1h2.fingers = 1
        `p2h1.fingers = 1
        `p2h2.fingers = 1
        `p3h1.fingers = 3 // this value is too high, can't get there directly from (1,1) and (1,1)
        `p3h2.fingers = 3 // this value is too high, can't get there directly from (1,1) and (1,1)
    }

    // invalid move
    example subtractFingers is {no p1, p2, p3 : Player | move[p1, p2, p3]} for {
        Player = `p1 + `p2 + `p3
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2 + `p3h1 + `p3h2

        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1 + `p3 -> `p3h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2 + `p3 -> `p3h2
        next = `p1 -> `p2 + `p2 -> `p3 + `p3 -> `p1

        `p1h1.fingers = 2
        `p1h2.fingers = 3
        `p2h1.fingers = 2 
        `p2h2.fingers = 1
        `p3h1.fingers = 1 // too small, needs to be at least 2 (stay same) or 3 (add 1)
        `p3h2.fingers = 1 // too small, needs to be at least 2 (stay same) or 3 (add 1)
    }
}

test expect {
    mostEfficientWin: {
        some p1, p2, p3, p4, p5, p6: Player | {
            init[p1, p2] 
            noNegativeFingers
            move[p1, p2, p3]
            move[p2, p3, p4]
            move[p3, p4, p5]
            move[p4, p5, p6]
            winning[p1]
            disjointHands
            reachablePlayers
            alwaysTwoHands
            reachableHands
        }
    } for 6 Player, 12 Hand is sat

    // Still works but takes more players / turns
    lessEfficientWin: {
        some p1, p2, p3, p4, p5, p6, p7, p8: Player | {
            init[p1, p2] 
            noNegativeFingers
            move[p1, p2, p3]
            move[p2, p3, p4]
            move[p3, p4, p5]
            move[p4, p5, p6]
            move[p5, p6, p7]
            move[p6, p7, p8]
            winning[p1]
            disjointHands
            reachablePlayers
            alwaysTwoHands
            reachableHands
        }
    } for 8 Player, 16 Hand is sat

    // Not enough players / turns
    impossibleToWin: {
        some p1, p2, p3, p4: Player | {
            init[p1, p2] 
            noNegativeFingers
            move[p1, p2, p3]
            move[p2, p3, p4]
            winning[p1]
            disjointHands
            reachablePlayers
            alwaysTwoHands
            reachableHands
        }
    } for 4 Player, 8 Hand is unsat
}