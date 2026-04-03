import Game.Metadata
import Game.Levels.Definitions

World "LinearCombinations"
Level 1

Title "What are Linear Combinations?"

Introduction "Suppose that V is a vector space over a field F and that v_1, v_2, v_3 ∈ V.
If α_1, α_2, α_3 ∈ F we say that the vector
  v = α_1 • v_1 + α_2 • v_2 + α_3 • v_3
is a linear combination of the vectors v_1, v_2, v_3.

Lets explore this through what we have learnt about subspaces!
We are going to consider a subspace W with three vectors and show that any
linear combination of them naturally lies in W.

This follows directly from the closure properties we proved:
smul_mem tells us each α_i • v_i ∈ W, and add_mem chains them together."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (W : MySubspace F V) (α_1 α_2 α_3 : F) (v_1 v_2 v_3 : V)
    (hv_1 : v_1 ∈ W) (hv_2 : v_2 ∈ W) (hv_3 : v_3 ∈ W) :
    α_1 • v_1 + α_2 • v_2 + α_3 • v_3 ∈ W := by
  Hint "Use add_mem and smul_mem in a chain. Each α_i • v_i ∈ W by smul_mem, then chain with add_mem."
  exact W.add_mem
    (W.add_mem
      (W.smul_mem hv_1)
      (W.smul_mem hv_2))
    (W.smul_mem hv_3)

Conclusion "Well done! You have shown that a linear combination of three vectors in a
subspace also lies in that subspace. This follows entirely from the closure properties
we proved in the Subspaces world — no new axioms needed."
