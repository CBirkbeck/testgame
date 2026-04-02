import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.VectorSpaces.L01_VectorSpaces

World "VectorSpaces"
Level 2

Title "Scalar multiplication over four vectors"

Introduction "Now we use smul_add to distribute scalar multiplication over four vectors.

The axiom smul_add handles two vectors at a time:
  smul_add : α • (v + w) = α • v + α • w

To distribute over four vectors we must apply it in stages, using add_asoc to
restructure the brackets first. The strategy has five steps:
Now we will use our smul_add axiom to distribute scalar multiplication over a sum of four vectors."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

/--
Scalar multiplication distributes over a sum of four vectors:
`α • (v₁ + v₂ + v₃ + v₄) = α•v₁ + α•v₂ + α•v₃ + α•v₄`.
-/


Statement MyVectorSpace.smul_add4 (v_1 v_2 v_3 v_4 : V) (α : F) :
    α • (v_1 + v_2 + v_3 + v_4) = α • v_1 + α • v_2 + α • v_3 + α • v_4 := by
  rw [MyVectorSpace.add_asoc (v_1 + v_2) v_3 v_4]
  rw [MyVectorSpace.smul_add α (v_1 + v_2) (v_3 + v_4)]
  rw [MyVectorSpace.smul_add α v_1 v_2]
  rw [MyVectorSpace.smul_add α v_3 v_4]
  rw [MyVectorSpace.add_asoc (α • v_1 + α • v_2) (α • v_3) (α • v_4)]

NewTheorem MyVectorSpace.smul_add4
Conclusion field
Conclusion "Excellent! You have proved smul_add4.
In Level 3 you will see how having smul_add4 as a named theorem makes the next proof
just two lines — this is the payoff of building up a library of lemmas.
Theorem smul_add4 is now unlocked."
