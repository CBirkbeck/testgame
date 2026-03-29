import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.SubSpaces.L04_SubSpaces

World "SubSpaces"
Level 5

Title "Intersection of two subspaces i"

Introduction "We will now be looking at showing that if V is a vector space, and U and W are subspaces of V, then U ∩ W is a subspace of V. To start let us show that it contains the 0 element. Think about what it means to intersect two sets."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (U : MySubspace F V) (W : MySubspace F V) : 0 ∈ U ∧ 0 ∈ W := by
  constructor
  exact U.zero_mem
  exact W.zero_mem
