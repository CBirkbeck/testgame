import Game.Metadata
import Game.Levels.Definitions

World "VectorSpaces"
Level 1

/--
Theorem stating that addition of vectors is commutative up to reordering
of four terms:
`v₁ + v₂ + v₃ + v₄ = v₂ + v₁ + v₄ + v₃`.
-/
TheoremDoc MyVectorSpace.add_perm4 as "add_perm4" in "Addition"

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement MyVectorSpace.add_perm4
  (v_1 v_2 v_3 v_4 : V) :
  v_1 + v_2 + v_3 + v_4 = v_2 + v_1 + v_4 + v_3 := by
  rw [MyVectorSpace.add_comm v_1 v_2]
  rw [MyVectorSpace.add_asoc (v_2 + v_1) v_3 v_4]
  rw [MyVectorSpace.add_comm v_3 v_4]
  rw [← MyVectorSpace.add_asoc (v_2 + v_1) v_4 v_3]
