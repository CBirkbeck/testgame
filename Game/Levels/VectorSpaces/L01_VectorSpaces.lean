import Game.Metadata
import Game.Levels.Definitions

World "VectorSpaces"
Level 1

Title "Permuting four vectors"

Introduction "In this level we explore how commutativity and associativity of vector addition
let us reorder sums of vectors."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

/--
Vector addition has a right identity:
`v + 0 = v`.
-/
TheoremDoc MyVectorSpace.add_zero as "add_zero" in "MyVectorSpace"

/--
Vector addition is commutative:
`u + v = v + u`.
-/
TheoremDoc MyVectorSpace.add_comm as "add_comm" in "MyVectorSpace"

/--
Every vector has an additive inverse:
`∀ v, ∃ w, v + w = 0 ∧ w + v = 0`.
-/
TheoremDoc MyVectorSpace.add_inv as "add_inv" in "MyVectorSpace"

/--
Vector addition is associative:
`(u + v) + w = u + (v + w)`.
-/
TheoremDoc MyVectorSpace.add_asoc as "add_asoc" in "MyVectorSpace"

/--
Scalar multiplication distributes over vector addition:
`α • (v + w) = α • v + α • w`.
-/
TheoremDoc MyVectorSpace.smul_add as "smul_add" in "MyVectorSpace"

NewTheorem MyVectorSpace.add_zero MyVectorSpace.add_comm MyVectorSpace.add_inv
           MyVectorSpace.add_asoc MyVectorSpace.smul_add

/--
Vectors can be permuted in a sum of four:
`v₁ + v₂ + v₃ + v₄ = v₂ + v₁ + v₄ + v₃`.
-/
TheoremDoc MyVectorSpace.add_perm4 as "add_perm4" in "Addition"

Statement MyVectorSpace.add_perm4 (v_1 v_2 v_3 v_4 : V) :
    v_1 + v_2 + v_3 + v_4 = v_2 + v_1 + v_4 + v_3 := by
  rw [MyVectorSpace.add_comm v_1 v_2]
  rw [MyVectorSpace.add_asoc (v_2 + v_1) v_3 v_4]
  rw [MyVectorSpace.add_comm v_3 v_4]
  rw [← MyVectorSpace.add_asoc (v_2 + v_1) v_4 v_3]

NewTheorem MyVectorSpace.add_perm4
