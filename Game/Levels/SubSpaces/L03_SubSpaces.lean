import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.SubSpaces.L02_SubSpaces

World "SubSpaces"
Level 3

Title "Closed under scalar multiplication"

Introduction "Similarly to the last level we are showing an integral property of subspaces: that they are closed under scalar multiplication."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (W : MySubspace F V) (α : F) (v : V) (hv : v ∈ W) :
    α • v ∈ W := by
  exact W.smul_mem hv

Conclusion "Well done! I hope at this point you are getting to grips with the style of Lean we will be using. You are doing very well!"
