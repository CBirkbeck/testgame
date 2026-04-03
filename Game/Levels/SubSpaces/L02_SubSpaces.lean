import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.SubSpaces.L01_SubSpaces
World "SubSpaces"
Level 2

Title "Closed under adition"

Introduction "In this level we show that a subspace is closed under addition.

Closure under addition means: if u ∈ W and v ∈ W, then u + v ∈ W.
This is not automatic for arbitrary subsets — it must be verified.

This level introduces something new: named hypotheses inside the statement.
  hu : u ∈ W   means hu is a proof that u ∈ W
  hv : v ∈ W   means hv is a proof that v ∈ W

Think of W.add_mem as a function:
  W.add_mem  :  u ∈ W → v ∈ W → u + v ∈ W
Apply it to hu and hv to produce a proof that u + v ∈ W.
"

variable {F V : Type*} [MyField F] [MyVectorSpace F V]
variable (W : MySubspace F V)

Statement (W : MySubspace F V) (u v : V) (hu : u ∈ W) (hv : v ∈ W) : (u + v ∈ W) := by
  Hint "hu and hv are assumptions given to you. Try: exact W.add_mem hu hv"
  exact W.add_mem hu hv

Conclusion "Well done! This was your first proof using named hypotheses.
In Lean, hu : u ∈ W means hu is a proof that u belongs to W.
You supply it as an argument to W.add_mem, just as in a standard mathematical proof."
