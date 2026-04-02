import Game.Metadata
import Game.Levels.Definitions

World "VectorSpaces"
Level 1

Title "Permuting four vectors"

Introduction "In this level we explore commutativity and associativity of vector addition.

Recall Remark 2 after Definition 1.5: using VS4 and VS5 we can reorder any sum.
Here we prove:  v_1 + v_2 + v_3 + v_4 = v_2 + v_1 + v_4 + v_3

IMPORTANT: when Lean writes v_1 + v_2 + v_3 + v_4 it means ((v_1 + v_2) + v_3) + v_4.
The brackets are invisible but matter when applying rw.
Hover over a + symbol in the interface to reveal the hidden bracket structure."


variable {F V : Type*} [MyField F] [MyVectorSpace F V]

/--
`MyVectorSpace.add_zero`: Vector addition has a right identity: `v + 0 = v`.
-/
TheoremDoc MyVectorSpace.add_zero as "V.add_zero" in "VectorSpace"

/--
`MyVectorSpace.add_comm`: Vector addition is commutative: `u + v = v + u`.
-/
TheoremDoc MyVectorSpace.add_comm as "V.add_comm" in "VectorSpace"

/--
`MyVectorSpace.add_inv`: Every vector has an additive inverse: `∀ v, ∃ w, v + w = 0 ∧ w + v = 0`.
-/
TheoremDoc MyVectorSpace.add_inv as "V.add_inv" in "VectorSpace"

/--
`MyVectorSpace.add_asoc`: Vector addition is associative: `(u + v) + w = u + (v + w)`.
-/
TheoremDoc MyVectorSpace.add_asoc as "V.add_asoc" in "VectorSpace"

/--
`MyVectorSpace.smul_add`: Scalar multiplication distributes over vector addition: `α • (v + w) = α • v + α • w`.
-/
TheoremDoc MyVectorSpace.smul_add as "V.smul_add" in "VectorSpace"

/--
`MyVectorSpace.add_perm4`: Vectors can be permuted in a sum of four: `v₁ + v₂ + v₃ + v₄ = v₂ + v₁ + v₄ + v₃`.
-/
TheoremDoc MyVectorSpace.add_perm4 as "V.add_perm4" in "VectorSpace"


Statement MyVectorSpace.add_perm4 (v_1 v_2 v_3 v_4 : V) :
    v_1 + v_2 + v_3 + v_4 = v_2 + v_1 + v_4 + v_3 := by
  Hint "Start with rw [MyVectorSpace.add_comm v_1 v_2], then use add_asoc to separate v_3 and v_4."
  rw [MyVectorSpace.add_comm v_1 v_2]
  rw [MyVectorSpace.add_asoc (v_2 + v_1) v_3 v_4]
  rw [MyVectorSpace.add_comm v_3 v_4]
  rw [← MyVectorSpace.add_asoc (v_2 + v_1) v_4 v_3]

Conclusion "Well done! You have proved add_perm4.
This theorem is now unlocked and will be used directly in Level 3.
The key lesson: even simple reorderings require careful bracket management in Lean.
Level 2 introduces the other main axiom — distributivity of scalar multiplication."

NewTheorem MyVectorSpace.add_zero MyVectorSpace.add_comm MyVectorSpace.add_inv MyVectorSpace.add_asoc MyVectorSpace.smul_add MyVectorSpace.add_perm4
