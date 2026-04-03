import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.VectorSpaces.L02_VectorSpaces

World "VectorSpaces"
Level 3

Title "Combining permutation and scalar distribution"

Introduction "In this level we combine the two ideas from the previous levels.

Your goal is:
  α • (v_1 + v_2 + v_3 + v_4) = α • v_2 + α • v_1 + α • v_4 + α • v_3

On paper: first reorder the vectors using commutativity, then distribute the scalar.

Step 1: swap v_1 and v_2 using add_comm
  rw [MyVectorSpace.add_comm v_1 v_2]

Step 2: regroup v_3 and v_4 using add_asoc
  rw [MyVectorSpace.add_asoc (v_2 + v_1) v_3 v_4]

Step 3: swap v_3 and v_4 using add_comm
  rw [MyVectorSpace.add_comm v_3 v_4]

Step 4: regroup back using ← add_asoc
  rw [← MyVectorSpace.add_asoc (v_2 + v_1) v_4 v_3]

Step 5: distribute the scalar using smul_add4
  rw [MyVectorSpace.smul_add4 v_2 v_1 v_4 v_3]"

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (v_1 v_2 v_3 v_4 : V) (α : F) :
    α • (v_1 + v_2 + v_3 + v_4) = α • v_2 + α • v_1 + α • v_4 + α • v_3 := by
  Hint "Start by swapping v_1 and v_2: rw [MyVectorSpace.add_comm v_1 v_2]"
  rw [MyVectorSpace.add_comm v_1 v_2]
  Hint "Now regroup v_3 and v_4: rw [MyVectorSpace.add_asoc (v_2 + v_1) v_3 v_4]"
  rw [MyVectorSpace.add_asoc (v_2 + v_1) v_3 v_4]
  Hint "Swap v_3 and v_4: rw [MyVectorSpace.add_comm v_3 v_4]"
  rw [MyVectorSpace.add_comm v_3 v_4]
  Hint "Regroup back: rw [← MyVectorSpace.add_asoc (v_2 + v_1) v_4 v_3]"
  rw [← MyVectorSpace.add_asoc (v_2 + v_1) v_4 v_3]
  Hint "Now distribute the scalar using smul_add4: rw [MyVectorSpace.smul_add4 v_2 v_1 v_4 v_3]"
  rw [MyVectorSpace.smul_add4 v_2 v_1 v_4 v_3]

Conclusion "Well done! You combined vector reordering with scalar distribution.

Notice that because smul_add4 was proved and named in Level 2, you could use it
directly here in one step. This is the payoff of building up a library of lemmas —
once proved, a theorem is available forever.

Level 4 is the hardest in this world — it proves the cancellation law (Theorem 1.6(i))."
