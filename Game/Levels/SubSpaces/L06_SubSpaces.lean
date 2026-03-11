import Game.Metadata
import Game.Levels.Definitions

World "SubSpaces"
Level 6

Title "Intersection of two subspaces ii"

Introduction "We have shown the suposed subspace contains zero, thus is non empty, now lets show that it is closed under adition and multiplication"

variable {F V : Type*} [MyField F] [MyVectorSpace F V]
variable (W : MySubspace F V)
variable (U : MySubspace F V)

Statement (W : MySubspace F V) (U : MySubspace F V) (α : F) (u v u' v' : V) (hu : W.carrier u) (hv : W.carrier v) (hu' : U.carrier u') (hv' : U.carrier v') : W.carrier (u + α • v) ∧ U.carrier (u' + α • v') := by
  constructor
  exact W.add_mem hu (W.smul_mem hv)
  exact U.add_mem hu' (U.smul_mem hv')
