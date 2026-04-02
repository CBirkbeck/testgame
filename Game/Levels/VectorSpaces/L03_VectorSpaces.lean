import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.VectorSpaces.L02_VectorSpaces

World "VectorSpaces"
Level 3

Title "Combining permutation and scalar distribution"

Introduction "In this level we combine the two theorems from the previous levels.

Your goal is:
  α • (v_1 + v_2 + v_3 + v_4) = α • v_2 + α • v_1 + α • v_4 + α • v_3

On paper: first reorder the vectors using commutativity, then distribute the scalar.
In Lean, because we already proved add_perm4 and smul_add4, the proof is two lines:

Your goal is:
  α • (v_1 + v_2 + v_3 + v_4) = α • v_2 + α • v_1 + α • v_4 + α • v_3

On paper: first reorder the vectors using commutativity, then distribute the scalar.
In Lean, because we already proved add_perm4 and smul_add4, the proof is two lines:"

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (v_1 v_2 v_3 v_4 : V) (α : F) :
    α • (v_1 + v_2 + v_3 + v_4) = α • v_2 + α • v_1 + α • v_4 + α • v_3 := by

  Hint "You have already proved add_perm4 and smul_add4. Apply them in order."
  rw [MyVectorSpace.add_perm4 v_1 v_2 v_3 v_4]
  rw [MyVectorSpace.smul_add4 v_2 v_1 v_4 v_3]
Conclusion "A two-line proof of a non-trivial statement!
Once theorems are proved in Lean, using them is as simple as citing a lemma in maths.
Level 4 is the hardest in this world — it proves Theorem 1.6(i) from the course notes."
