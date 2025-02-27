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

**Signatures and Predicates:**

At a high level, what do each of your sigs and preds represent in the context of the model? Justify the purpose for their existence and how they fit together.

disjointHands

reachableHands

reachablePlayers

alwaysTwoHands

winning

init

noNegativeFingers

move

**Testing:**

What tests did you write to test your model itself? What tests did you write to verify properties about your domain area? Feel free to give a high-level overview of this.

**Documentation:**

Make sure your model and test files are well-documented. This will help in understanding the structure and logic of your project.



