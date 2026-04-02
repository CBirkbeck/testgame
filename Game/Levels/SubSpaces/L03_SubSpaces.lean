import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.SubSpaces.L02_SubSpaces

World "SubSpaces"
Level 3

Title "Closed under scalar multiplication"

Introduction "Similarly to the last level, we show a subspace is closed under scalar multiplication.

If v ∈ W and α ∈ F, then α • v ∈ W.

You are given: hv : v ∈ W

The subspace axiom smul_mem has the form:
  W.smul_mem : v ∈ W → α • v ∈ W

Apply it to hv. Lean infers the scalar α from context automatically.
"

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (W : MySubspace F V) (α : F) (v : V) (hv : v ∈ W) :
    α • v ∈ W := by
  exact W.smul_mem hv

Conclusion "Well done! You have now proved all three Subspace Test conditions individually:
  Level 1: 0 ∈ W                       (W.zero_mem)
  Level 2: u, v ∈ W ⟹ u + v ∈ W      (W.add_mem)
  Level 3: v ∈ W ⟹ α • v ∈ W         (W.smul_mem)

Level 4 combines all three in a single proof using the constructor tactic."
