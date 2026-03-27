import Game.Metadata
import Game.Levels.Definitions

World "SubSpaces"
Level 1

Title "Exploring Subspaces"

Introduction "We are going to begin by looking at the properties of a subspace. Suppose that V is a
vector space over a field F and that W is a subset of V. We say that W is a (vector) subspace of V
if it is a vector space in its own right with respect to vector addition and scalar multiplication
inherited from V. Thus we will begin by looking at the importance of containing the zero vector."

TacticDoc exact "The `exact` tactic closes a goal by providing a direct proof term."
TacticDoc constructor "The `constructor` tactic splits a conjunction goal `P ∧ Q` into two subgoals."

NewTactic exact constructor

variable {F V : Type*} [MyField F] [MyVectorSpace F V]
variable (W : MySubspace F V)

Statement : 0 ∈ W := by
  exact W.zero_mem

Conclusion "Congratulations, you have shown one of the important properties of a vector subspace!"
