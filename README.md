# curiositymodeling
Curiosity Modeling Project for CSCI 1710


2 players, each payer has 2 hands, each hand has up to five fingers

Init:
each player's hand1 + hand2 has 1 finger

Valid transition:

One players fingers increases by the other players fingers on one hand

/////////////////////////////////////////////////////////////////////////////////////////////

**Project Objective:**

Our project models a modified verision of the Chopsticks game. In this game, there are two players. Each player has two hands and starts with one finger on each hand. Then Player 1 can use on of their hands to point to one of Player 2's hand and transfer over the number of fingers on Player 1's hand to Player 2's hand. They switch turns doing this until one player has 7 or more fingers across both of their hands. When this happens, the player with 7 or more fingers loses the game. The other player wins.

**Model Design and Visualization:**

Give an overview of your model design choices, what checks or run statements you wrote, and what we should expect to see from an instance produced by the Sterling visualizer. How should we look at and interpret an instance created by your spec? Did you create a custom visualization, or did you use the default?

In our model, the Player sig functions more like a "turn", where all of one player's turns are represented by positive numbers and the other player's turns are represented by negative numbers. Each Player has two hands, hand1 and hand 2. Each Player also has a next field to switch turns between each other. 

The Hand sig has a field to represent the fingers on each hand. 

**Signatures and Predicates:**

disjointHands
- This predicate checks that each player's hand is separate from it's other hand and from both of the opposing player's hands. 

reachableHands
- This predicate chekcs that all hands in the model are pointed to by some player and that there are never lone hands in the game.

reachablePlayers
- This predicate checks that all players are connected to each other using the "next" attribute. The last player loops back to the first player, so the first player is reachable as well. This ensures that the players are going in sequential order and that they are switching turns. 

alwaysTwoHands
- This predicate checks that all players have exactly two hands. A player can not have more or less than two hands at all times. 

winning[p1]
- This predicate checks that it is possible for a player to win the game. A player wins the game when they have a total of less than 7 fingers across both of their hands and the opposing player has a total of 7 or more fingers across both of their hands. This also checks that the losing player loops back to the first player. This is an indication that the game has ended and that the game needs to start over. This predicate relies on the move predicate to correctly increase the number of total fingers on each player's hands during their turn.

init[p1, p2]
- This predicate sets up the game where each player has one finger on each of their hands. It also creates a link between the two players where Player 1 points to Player 2 through the next attribute. This forms the basis of the game, and the move predicate can be used to continue further actions.

noNegativeFingers
- This predicate checks that each hand has a positive number of fingers. Becuase integers in Forge span from -8 to 7. We don't want to include negative numbers because that would interfere with the addition that we need to do during each move to count up total fingers. 

move[p1, p2, p3]
- This predicate checks that a valid move is being played. A valid move is when the current player's total number fingers is being increased by the number of fingers on one of the opposing player's hands. The current player is represented by p1 and p3 (as referenced in our interpretation of the Player sig being more simliar to a "turn" and odd Players / turns refer to one player). Hands cannot lose fingers (this is checking that noNegativeFigners is working as well).

**Testing:**

We wrote unit tests for each of the predicates as well as system tests to check that everything runs with all of the predicates and specific arguments. For each predicate, we wrote mutiple tests for scenarios that should pass and fail according to the predicate's properties. For the system tests, we checked three scenarios: the most ideal and efficient, as defined by the number of moves / turns, way to win (6 Players), another possible way to win but not the most efficient (8 Players), and the case where it is impossible to win with such minimal number of moves (4 Players).

**Documentation:**

Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.



