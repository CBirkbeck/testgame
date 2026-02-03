import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.DemoWorld.L02_HelloWorld

World "VectorSpaces"
Level 2

/--
Theorem stating that scalar multiplication distributes over the sum of four vectors:
`α • (v₁ + v₂ + v₃ + v₄) = α•v₁ + α•v₂ + α•v₃ + α•v₄`.
-/
TheoremDoc MyVectorSpace.smul_add4 as "smul_add4" in "Scalar Multiplication"

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement MyVectorSpace.smul_add4 (v_1 v_2 v_3 v_4 : V) (α : F) : α • (v_1 + v_2 + v_3 + v_4) =α • v_1 + α • v_2 + α • v_3 + α • v_4 := by
  rw [MyVectorSpace.add_asoc (v_1 + v_2) v_3 v_4]
  rw [MyVectorSpace.smul_add α (v_1 + v_2) (v_3 + v_4)]
  rw [MyVectorSpace.smul_add α v_1 v_2]
  rw [MyVectorSpace.smul_add α v_3 v_4]
  rw [MyVectorSpace.add_asoc (α • v_1 + α • v_2) (α • v_3) (α • v_4)]
