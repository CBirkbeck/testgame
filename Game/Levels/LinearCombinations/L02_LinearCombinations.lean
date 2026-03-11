import Game.Metadata
import Game.Levels.Definitions

World "LinearCombinations"
Level 2

Title "What is spanning?"

Introduction "We have seen what it means to be a linear combination, if every vector in V can be written as a linar combination we we say these vectors span V."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

def Spans3 (v₁ v₂ v₃ : V) : Prop :=
∀ v : V, ∃ α₁ α₂ α₃ : F, v = α₁ • v₁ + α₂ • v₂ + α₃ • v₃

/--
If v_1, v_2,v_3 span V, then every vector is a linear combination of them.
-/
Statement (v₁ v₂ v₃ v : V)
(hspan : Spans3 (F:=F) (V:=V) v₁ v₂ v₃) :
∃ α₁ α₂ α₃ : F, v = α₁ • v₁ + α₂ • v₂ + α₃ • v₃ := by
exact hspan v
