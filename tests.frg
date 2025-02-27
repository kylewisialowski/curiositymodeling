#lang forge/froglet

open "chopsticks.frg"

/* Tests for the disjointHands predicate */
test suite for disjointHands {

    /* 
        A valid distribution of hands between all of the players. Player1's hand1 is distinct 
        from Player1's hand2 is distinct from Player2's hand1 is distinct from Player2's hand2.
    */
    example validDisjointHands is {disjointHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2
    }

    /* 
        Player1's hand1 should not be the same as Player2's hand1. 
    */
    example overlapDiffPlayersH1toH1 is {not disjointHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h2
        hand1 = `p1 -> `p1h1 + `p2 -> `p1h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2 // p1h1 = p2h1
    }

    /* 
        Player1's hand1 should not be the same as Player2's hand2
    */
    example overlapDiffPlayersH1toH2 is {not disjointHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h1
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p1h1 // p1h1 = p2h2
    }

    /*
        Player1's hand2 should not be the same as Player2's hand1
    */
    example overlapDiffPlayersH2toH1 is {not disjointHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h2
        hand1 = `p1 -> `p1h1 + `p2 -> `p1h2 // p1h2 = p2h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2 
    }

    /*
        Player1's hand2 should not be the same as Player2's hand2
    */
    example overlapDiffPlayersH2toH2 is {not disjointHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h1 
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p1h2 // p1h2 = p2h2
    }

    /*
        Player1's hand1 should not be the same as Player1's hand2
    */
    example overlapSamePlayer is {not disjointHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p2h1 + `p2h2
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1 
        hand2 = `p1 -> `p1h1 + `p2 -> `p2h2 // p1h1 = p1h2
    }

    /* 
        Player2's hand1 should not be the same as Player2's hand2
    */
    example overlapSamePlayer1 is {not disjointHands} for {
        Player = `p1 + `p2
        Hand = `p1h1 + `p1h2 + `p2h1
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1 
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h1 // p2h1 = p2h2
    }
}

/* Tests for the reachableHands predicate */
test suite for reachableHands {
    /*
        Each hand is linked to either Player1 or Player2
    */
    example canReachHands is {reachableHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2
    }

    /*
        One hand is not attached to any players
    */
    example oneLoneHand is {not reachableHands} for {
        Player = `p1 + `p2 
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2 // p2h2 is left on its own 
        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1
        hand2 = `p1 -> `p1h2 
    }

    /*
        All hands are not attached to any players
    */
    example allLoneHands is {not reachableHands} for {
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2
    }
}

/*
    Tests for the reachablePlayers predicate
*/
test suite for reachablePlayers {
    /* 
        Player1 and Player2 are linked to each other
    */
    example canReachPlayers is {reachablePlayers} for {
        Player = `p1 + `p2
        next = `p1 -> `p2 + `p2 -> `p1
    }

    /*
        All players are linked to each other in sequential order using the 'next' field
    */
    example multiplePlayers is {reachablePlayers} for {
        Player = `p1 + `p2 + `p3 + `p4
        next = `p1 -> `p2 + `p2 -> `p3 + `p3 -> `p4 + `p4 -> `p1
    }

    /*
        Player1 and Player2 are not connected to each other or any other player
    */
    example cannotReachPlayers is {not reachablePlayers} for {
        Player = `p1 + `p2
    }
}

/* Tests for the alwaysTwoHands predicate */
test suite for alwaysTwoHands {
    /*
        A player has hands assigned to the 'hand1' and 'hand2' fields
    */
    example twoHands is {alwaysTwoHands} for {
        Player = `p1
        Hand = `p1h1 + `p1h2
        hand1 = `p1 -> `p1h1
        hand2 = `p1 -> `p1h2
    }

    /*
        Two hands are declared but only one is linked to the player
    */
    example oneHand is {not alwaysTwoHands} for {
        Player = `p1
        Hand = `p1h1 + `p1h2
        hand1 = `p1 -> `p1h1
    }

    /*
        Two hands are declared but they are not linked to the player
    */
    example noHands is {not alwaysTwoHands} for {
        Player = `p1
        Hand = `p1h1 + `p1h2
    }
}

/* Tests for the winning predicate */
test suite for winning {

    /*
        Loser has 7 total fingers, Winner has 3 total fingers
    */
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

    /*
        Player2 has 6 total fingers, Player3 has 3 total fingers
        Neither are >= 7 so no one wins
    */
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

/* Tests for the init predicate */
test suite for init {
    /*
        There are two players each with two hands and each of those hands as one finger
    */
    example validInit is {all disj p1, p2 : Player | init[p1, p2]} for {
        Player = `p1 + `p2
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2 

        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1 
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2 
        next = `p1 -> `p2 + `p2 -> `p1

        fingers = `p1h1 -> 1 + `p1h2 -> 1 + `p2h1 -> 1 + `p2h2 -> 1
    }

    /*
        One of the hands has 2 fingers to start, which should not be allowed
    */
    example initNotOne is {no p1, p2 : Player | init[p1, p2]} for {
        Player = `p1 + `p2
        Hand = `p1h1 + `p1h2 + `p2h1 + `p2h2 

        hand1 = `p1 -> `p1h1 + `p2 -> `p2h1 
        hand2 = `p1 -> `p1h2 + `p2 -> `p2h2 
        next = `p1 -> `p2 + `p2 -> `p1

        fingers = `p1h1 -> 1 + `p1h2 -> 3 + `p2h1 -> 1 + `p2h2 -> 2
    }

}

/* Tests for the noNegativeFingers predicate */
test suite for noNegativeFingers {
    /*
        The hand has 1 finger
    */
    example positiveFingers is {noNegativeFingers} for {
        Hand = `h
        `h.fingers = 1
    }

    /*
        The hand has -1 finger
    */
    example negativeFingers is {not noNegativeFingers} for {
        Hand = `h
        `h.fingers = -1
    }
    
    /*
        0 fingers is not necessarily negative but is not allowed in our game either
    */
    example zeroFingers is {not noNegativeFingers} for {
        Hand = `h
        `h.fingers = 0
    }
}

/* Tests for the move predicate */
test suite for move {
    /*
        Player3's total fingers increases by one of Player2's hand1's fingers
    */
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

    /*
        Player3's total fingers increases by one of Player2's hand2's fingers
    */
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

    /*
        Invalid move because there is no possible way to get to the number of fingers on each
        of Player3's hands from the given Player1 and Player2's hands
    */
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

    /*
        Invalid move because in order to get to the number of fingers on each of Player3's 
        hands is to add a negative (subtract) but that is alreayd not allowed by the 
        noNegativeFingers predicate
    */
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

/* System tests for the whole game */
test expect {
    /*
        The way to win the game in the least amount of moves is by using 6 Players, which 
        consequently wil use 12 Hands
    */
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

    /*
        There are other possible ways to win the game but it will require more players / turns
    */
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

    /*
        There are not enough players / turns to increase a player's total number of fingers 
        to be >= 7 so there is no winner
    */
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