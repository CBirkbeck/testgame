import Game.Metadata
import Game.Levels.Definitions

World "SubSpaces"
Level 1

Title "Exploring Subspaces"

Introduction "We are going to begin by looking at the properties of a subspace.

Suppose V is a vector space over a field F and W is a subset of V.
W is a subspace of V if it is a vector space in its own right, inheriting
vector addition and scalar multiplication from V.

Our Lean definition of a subspace has three fields:
  zero_mem : 0 ∈ carrier
  add_mem  : u ∈ W → v ∈ W → u + v ∈ W
  smul_mem : v ∈ W → α • v ∈ W

These correspond exactly to the three conditions of the Subspace Test
(Theorem 1.9 in the course notes).

In this level we verify the first condition: the subspace W must contain 0.

New tactic: exact
  exact term  closes a goal when term has exactly the right type.
  Here, W.zero_mem has type 0 ∈ W, which matches the goal.
"

TacticDoc exact "The `exact` tactic closes a goal by providing a direct proof term."
TacticDoc constructor "The `constructor` tactic splits a conjunction goal `P ∧ Q` into two subgoals."

NewTactic exact constructor

variable {F V : Type*} [MyField F] [MyVectorSpace F V]
variable (W : MySubspace F V)

Statement : 0 ∈ W := by
  exact W.zero_mem

Conclusion "Congratulations! You have shown every subspace contains the zero vector.
Remember: a subset without 0 cannot be a subspace.
The exact tactic closes any goal when you can supply a proof term of exactly the right type.
You will use exact in every remaining level of this world."
