import Game.Metadata
import Game.Levels.Definitions

World "VectorSpaces"
Level 1

Title "Permuting four vectors"

Introduction "In this level we explore how commutativity and associativity of vector addition let us reorder sums of vectors."

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
  rw [MyVectorSpace.add_comm v_1 v_2]
  rw [MyVectorSpace.add_asoc (v_2 + v_1) v_3 v_4]
  rw [MyVectorSpace.add_comm v_3 v_4]
  rw [← MyVectorSpace.add_asoc (v_2 + v_1) v_4 v_3]

Conclusion "Well done! You have unlocked the vector space axioms and can now use them in future levels."

NewTheorem MyVectorSpace.add_zero MyVectorSpace.add_comm MyVectorSpace.add_inv MyVectorSpace.add_asoc MyVectorSpace.smul_add MyVectorSpace.add_perm4
