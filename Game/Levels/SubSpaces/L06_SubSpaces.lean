import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.SubSpaces.L05_SubSpaces

World "SubSpaces"
Level 6

Title "Intersection of two subspaces ii"

Introduction "We have shown the supposed subspace contains zero, thus is non empty. Now let us show that it is closed under addition and scalar multiplication."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (W : MySubspace F V) (U : MySubspace F V) (α : F) (u v u' v' : V)
    (hu : u ∈ W) (hv : v ∈ W) (hu' : u' ∈ U) (hv' : v' ∈ U) :
    u + α • v ∈ W ∧ u' + α • v' ∈ U := by
  constructor
  exact W.add_mem hu (W.smul_mem hv)
  exact U.add_mem hu' (U.smul_mem hv')
