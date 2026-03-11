import Game.Metadata
import Game.Levels.Definitions

World "SubSpaces"
Level 5

Title "Intersection of two subspaces i"

Introduction "We will now be looking at showing that if V is a vector space, and U and W are subspaces of V, then U ∩ W is a subspace of V. To start lets show that it contains the 0 element. Now to understand this level start by thinking about what it means to intersect two sets."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]
variable (W : MySubspace F V)
variable (U : MySubspace F V)

Statement (U : MySubspace F V) (W : MySubspace F V) : (U.carrier 0 ∧ W.carrier 0 ) := by
  constructor
  exact U.zero_mem
  exact W.zero_mem
