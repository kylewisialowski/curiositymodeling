#lang forge/froglet

open "chopsticks.frg"

test suite for disjointHands {

}

test suite for reachableHands {

}

test suite for reachablePlayers {

}

test suite for alwaysTwoHands {

}

test suite for winning {

}

test suite for init {

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

}

test expect {
    run: {run}
    for exactly 6 Player, exactly 12 Hand is sat
    for exactly 8 Player, exactly 16 Hand is sat
    for exactly 4 Player, exactly 8 Hand is unsat
}