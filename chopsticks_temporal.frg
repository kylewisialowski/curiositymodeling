#lang forge/temporal

option max_tracelength 12
option min_tracelength 2

---------- Definitions ----------

sig Player {
    var hand1 : lone Int,
    var hand2 : lone Int,
    var turn : lone Int
}

pred validState {

    // fingers between 0 and 5
    all p : Player | {
        p.hand1 >= 0
        p.hand1 <= 5
        p.hand2 >= 0
        p.hand2 <= 5
    }

    // two hands at all times
    all p : Player | {
        one p.hand1 and one p.hand2
    }

    #{ p : Player | p.turn = 1} = 1

    all p : Player | {
        p.turn = 0 or p.turn = 1
    }

}

pred initState {
        
    all p : Player | {
        p.hand1 = 1
        p.hand1 = 1
        p.hand2 = 1
        p.hand2 = 1
    }

}

pred validTurn {

    all p : Player | {


        p.turn = 1 implies {
        p.turn' = 0

        some p2 : Player | {

                p2 != p

                // not (p2.hand1' != p2.hand1 and p2.hand2' != p2.hand2) and (
                //     p2.hand1' = add[p2.hand1, p.hand1] or
                //     p2.hand1' = add[p2.hand1, p.hand2] or
                //     p2.hand2' = add[p2.hand2, p.hand1] or
                //     p2.hand2' = add[p2.hand2, p.hand2]
                // )

                p2.hand1' = add[p2.hand1, p.hand1] and (
                    not (
                        p2.hand1' = add[p2.hand1, p.hand2] or
                        p2.hand2' = add[p2.hand2, p.hand1] or
                        p2.hand2' = add[p2.hand2, p.hand2]
                    )
                )
                

                (p2.hand1' = add[p2.hand1, p.hand1]) implies p2.hand2' = p2.hand2 or
                (p2.hand1' = add[p2.hand1, p.hand2]) implies p2.hand2' = p2.hand2 or 
                (p2.hand2' = add[p2.hand2, p.hand1]) implies p2.hand1' = p2.hand1 or
                (p2.hand2' = add[p2.hand2, p.hand2]) implies p2.hand1' = p2.hand1
        
                
                p2.turn' = 1

                p.hand1' = p.hand1 and p.hand2' = p.hand2
                // p2.hand1' != p2.hand1 implies p2.hand2' = p2.hand2
                // p2.hand2' != p2.hand2 implies p2.hand1' = p2.hand1
     

            }      

        }

        // p.turn' = 0 implies (p.hand1' = p.hand1 and  p.hand2' = p.hand2)

        }


    }

pred winning {
    some disj p, p2: Player | {
        no p.hand1 and no p.hand2
        one p2.hand1 or one p.hand2
    }
}

run {
    initState
    always validState
    always validTurn
} for exactly 2 Player


// pred traces {
//     initState
//     always validState
//     always validTurn
// }


// test expect {
//     myTest: {
//         traces
//     } is unsat 
// }


