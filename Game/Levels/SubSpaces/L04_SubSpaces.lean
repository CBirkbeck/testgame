import Game.Metadata
import Game.Levels.Definitions

World "SubSpaces"
Level 4

Title "Subspace test"

Introduction "We will now be looking at the Subspace test: u,v ∈ W , λ ∈ F  u+λv ∈ W. So what we are making sure is is that this is closed under scalar adition and multiplication just like before!"

variable {F V : Type*} [MyField F] [MyVectorSpace F V]
variable (W : MySubspace F V)

Statement (W : MySubspace F V) (α : F) (u v : V) (hv : v ∈ W) (hu : u ∈ W): (u+ α • v ∈ W)∧(0 ∈ W)  := by

  Hint "This level may take some thinking, but you can apply our axioms in a chain i.e our add axiom on our scalar mult axiom"
  constructor
  exact W.add_mem hu (W.smul_mem hv)
  exact W.zero_mem
