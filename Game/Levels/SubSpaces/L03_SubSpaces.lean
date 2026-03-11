import Game.Metadata
import Game.Levels.Definitions

World "SubSpaces"
Level 3

Title "Closed under multiplication"

Introduction "Similiarly to the last level we are showing an integral property of subspaces, the property that they are closed under multiplication"

variable {F V : Type*} [MyField F] [MyVectorSpace F V]
variable (W : MySubspace F V)

Statement (W : MySubspace F V) (α : F) (v : V) (hv : W.carrier v) :
  W.carrier (α • v) := by
  exact W.smul_mem hv
Conclusion "well done, I hope at this point you are getting to grips with the style of LEAN we will be using. You are doing very well!"
