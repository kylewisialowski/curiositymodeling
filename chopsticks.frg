#lang forge/froglet

/*
  Tic-Tac-Toe Model
  (Approximating the live-code version from Spring 2024, for use in lab)  
*/

sig Order {
    prev : lone Player,
    current: ; lone Player,
    next : lone Player
}

sig Hand {
    fingers : lone Int
}

-- Two players: X and O (their names double as the marks put on the board)
abstract sig Player {
    hand1 : lone Hand,
    hand2 : lone Hand,
    next : lone Player
}

one sig p1, p2 extends Player {} 

-- Helper function (in this case, produces an integer)
-- Given a board and player, how many marks has that player made on the board?
fun countFingers[p1: Player, p2: Player]: one Int {
    #{add[p1.hand1.fingers, p1.hand2.fingers, p2.hand1.fingers, p2.hand2.fingers]}
}

-- Helper predicate (predicates always produce booleans)
-- Is it X's turn in this board?
pred p1turn[o: Order] {
    o.prev = p2
    o.current = p1
    o.next = p2
} 
-- Is it O's turn in this board?
pred p2turn[o: Order] {
    o.prev = p1
    o.current = p2
    o.next = p1
}
-- A board is *valid* if it's either X's turn or O's turn
--   (because of how we defined oturn, a board where someone has cheated will be excluded)
pred valid[o: Order] {
    p1turn[o] or p2turn[o]
}

-- A win for player <p> via a horizontal line
pred winp1[p1: Player, p2: Player] {
    #{add[p1.hand1.fingers, p1.hand2.fingers]} >= 10
    #{add[p2.hand1.fingers, p2.hand2.fingers]} < 10
}

-- A win for player <p> via a vertical line
pred winp2[p1: Player, p2: Player] {
    #{add[p2.hand1.fingers, p2.hand2.fingers]} >= 10
    #{add[p1.hand1.fingers, p1.hand2.fingers]} < 10
}

-- a win for player <p> via any of the above kinds of line       
pred winning[p1: Player, p2: Player] {
  winp1[p1: Player, p2: Player] or winp2[p1: Player, p2: Player]
}

------------------------------------------------------------------------------

-- When is a board an allowed starting state?
pred init[p1: Player, p2: Player] {
    -- can only start a game with the empty board
	p1.hand1.fingers = 1
    p1.hand2.fingers = 1
    p2.hand1.fingers = 1
    p2.hand2.fingers = 1
}

-- When can one board transition to another, according to the rules of the game?
--    (Only on a move: <p> placing their mark at position <r> <c>)
pred move[p1: Player, p2: Player] {
    -- GUARD (required to be able to make the move): 
    

    
    no pre.places[r][c]         -- no move there yet
    p = X implies xturn[pre]    -- correct turn
    p = O implies oturn[pre]    -- correct turn
	-- TRANSITION (what does the post-move board look like?)
    --     Add the mark:
	post.places[r][c] = p    
    --     Assert that no other squares change (this is called a "frame condition"):
    all r2, c2: Index | (r2!=r or c2!=c) implies {
        post.places[r2][c2] = pre.places[r2][c2]
    }
}

------------------------------------------------------------------------------

-- Conjecture: a valid board cannot move to become invalid.
-- Ask Forge to find a pair of boards: pre and post, where pre is valid, 
-- pre moves to post, and post is invalid.
run {    
    some pre, post: Board | {
        valid[pre]
        not valid[post]
        some row, col: Index, p: Player |  {
            move[pre, post, p, row, col]
        }
    }
} 
-- Allow 2 boards to exist, 3 indexes, and 2 players
for 2 Board, 3 Index, 2 Player 

-- The above should be unsatisfiable (or "UNSAT")

------------------------------------------------------------------------------
-- LAB BEGINS (Forge part)
------------------------------------------------------------------------------

-- (1) Read the provided code from above! You will use the predicates we have provided to fill in the run statements below.
--     Take your time in understanding the model. If you have any questions that you can't resolve with your partners, call over
--     a TA to discuss (using the hours queue). 

-- (2) Is it possible for a valid board to have *both* X and O as winners?
// run {    
//     // [FILL FOR LAB]
// } for 1 Board, 3 Index, 2 Player  

-- (3) Starting from the initial state, observe unique moves from the first player.
--    Hint: Use the Next button in the visualizer.
// run {    
//     // [FILL FOR LAB]
// } for 2 Board, 3 Index, 2 Player  

-- (4) What would happen if you rewrote the move predicate in a different way? 
--   Concretely, since there are only two players, it might seem OK to change the:
--       p = X implies xturn[pre]    
--       p = O implies oturn[pre]
--   to just:
--       p = X implies xturn[pre]
--   Is the version with both lines equivalent to the version with only one? Ask Forge to check.
--   Hint: write a new predicate containing the new change, and use a run command to compare them.
// predicate changedMove[pre: Board, post: Board, p: Player, r: Index, c: Index] {
//     // [FILL FOR LAB]
// }
// run {    
//     // [FILL FOR LAB]
// } for 2 Board, 3 Index, 2 Player  

-- (4.5) View the instance that Forge produces for the above run. Investigate why the two predicates
-- are not equivalent, and then explain your reasoning in the comment below:
/*
    // [FILL FOR LAB]
*/

