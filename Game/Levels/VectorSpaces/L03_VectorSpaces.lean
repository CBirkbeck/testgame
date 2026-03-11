import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.VectorSpaces.L02_VectorSpaces

World "VectorSpaces"
Level 3

variable {F V : Type*} [MyField F] [MyVectorSpace F V]
Statement (v_1 v_2 v_3 v_4 : V) (α : F) : α • (v_1 + v_2 + v_3 + v_4) = α • v_2 + α • v_1 + α • v_4+ α • v_3 := by
  rw[MyVectorSpace.add_perm4 v_1 v_2 v_3 v_4]
  rw[MyVectorSpace.smul_add4 v_2 v_1 v_4 v_3]
