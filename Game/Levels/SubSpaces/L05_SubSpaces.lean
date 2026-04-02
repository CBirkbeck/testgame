import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.SubSpaces.L04_SubSpaces

World "SubSpaces"
Level 5

Title "Intersection of two subspaces i"

Introduction "We will now show that the intersection of two subspaces is a subspace.

Recall: x ∈ U ∩ W means both x ∈ U and x ∈ W.
To show 0 ∈ U ∩ W we must show 0 ∈ U and 0 ∈ W simultaneously.

In Lean this is the conjunction:  0 ∈ U ∧ 0 ∈ W

Use constructor to split into two subgoals.
Both U and W are subspaces, so both contain 0."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (U : MySubspace F V) (W : MySubspace F V) : 0 ∈ U ∧ 0 ∈ W := by
Hint "Use constructor to split the goal, then close each part with the appropriate zero_mem."
  constructor
  exact U.zero_mem
  exact W.zero_mem
