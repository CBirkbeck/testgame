import Game.Metadata
import Game.Levels.Definitions

World "SubSpaces"
Level 2

Title "Closed under adition"

Introduction "In this level we are showing that vector subspaces are closed under adition. This may seemintuitive but it is vital to understand that we are dealing with subsets now and not just sets with axioms."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]
variable (W : MySubspace F V)

Statement (W : MySubspace F V) (u v : V) (hu : u ∈ W) (hv : v ∈ W) : (u + v ∈ W) := by
  Hint "Use one of our subspace axioms on hu and hv, hu and hv are simply asumptions we propose"
  exact W.add_mem hu hv

Conclusion "This is the first time we have seen proposed asumptions in this game so you did very well to dedal with them!"
