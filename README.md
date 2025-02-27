**Project Objective:**

Our project models a modified verision of the Chopsticks game. In this game, there are two players. Each player has two hands and starts with one finger on each hand. Then Player 1 can use on of their hands to point to one of Player 2's hand and transfer over the number of fingers on Player 1's hand to Player 2's hand. They switch turns doing this until one player has 7 or more fingers across both of their hands. When this happens, the player with 7 or more fingers loses the game. The other player wins.

**Model Design and Visualization:**

Design Choices:

Inititally, we tried to model this game with a singular Player1 and Player 2. Especially with the visualizer, this was challenging to implement in a fashion that would produce a clear result. Instead, we designed the game such that there are more than 2 player instances that represent both a "player" and a game state. One way to think about this would be that odd players represent Player 1 and even players represent Player 2. In this sense, we can see the player instances as "Players." Each player also has a next field that points to another player. In this sense, we can see the player instances as game states.

Modifications to the original game: We initially tried to model the exact game of Chopsticks but ran into trouble when trying to make specifications about each hand as well as the rules of "splitting" (when a player can use their move to redistribute their fingers between two hands). For this reason, we decided to omit the split rule. Given the flexibility of our predicates, our model produces instances where a player redistributes the fingers on their hands, but this redistribution does not count as a turn of its own. Also, the max fingers is 7 as to avoid the bitwidth concerns (which we did attempt to work around, but were having syntax issues). If we could pursue this project in more depth for the final, we would be interested in accounting for a more comprehensive model that tracks the maximum fingers (5) on individual hands (after which a player loses a hand), interpreting a "split" as a turn, and implementing a custom visualizaiton.

Running/interpretting our project: The run statement at the bottom of chopsticks.frg runs the program with 6 "players" (better interpreted as 6 moves). When looking at the visualizer, try to find the two players whose hands all point to "1." These are the starting players. Once you find these players, you can move through the visualizer via the "next" fields to see subsequent states of the game. Eventually, you will reach a player who has more than 7 total fingers. This is when the game "ends" because that player has lost. The end of the game is marked by a loop back to the first player.

**Signatures and Predicates:**

Hand sig
- This signature represents a hand and contains a "fingers" field. This field points to an integer that represents the number of fingers on the hand.

Player sig
- This signature represents a player and contains a field for hand1 and hand2 (which each point to a hand object), as well as a next field that points to the next player in the game.

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

We wrote unit tests for each of the predicates as well as system tests to check that everything runs with all of the predicates and specific arguments. For each predicate, we wrote mutiple tests for scenarios that should pass and fail according to the predicate's properties. For the system tests, we checked three scenarios: the most ideal and efficient, as defined by the number of moves / turns, way to win (6 Players), another possible way to win but not the most efficient (8 Players), and the case where it is impossible to win with such minimal number of moves (4 Players). Feel free to check our documentation for more details.

**Contributors: kwisialo, kmao5**