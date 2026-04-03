import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.LinearCombinations.L01_LinearCombinations

World "LinearCombinations"
Level 2

Title "What is spanning?"

Introduction "We have seen what it means to be a linear combination.
If every vector in V can be written as a linear combination of v_1, v_2, v_3,
we say these vectors span V.

In this level we make that precise: given a proof hspan that v_1, v_2, v_3 span V,
we use it to exhibit the coefficients for any specific vector v."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

def Spans3 (v₁ v₂ v₃ : V) : Prop :=
  ∀ v : V, ∃ α₁ α₂ α₃ : F, v = α₁ • v₁ + α₂ • v₂ + α₃ • v₃

Statement (v₁ v₂ v₃ v : V)
    (hspan : Spans3 (F := F) (V := V) v₁ v₂ v₃) :
    ∃ α₁ α₂ α₃ : F, v = α₁ • v₁ + α₂ • v₂ + α₃ • v₃ := by
  Hint "hspan says every vector can be written as a linear combination. Try: exact hspan v"
  exact hspan v

Conclusion "Well done! You have used the spanning hypothesis directly.
This is exactly Definition 1.12 from the course notes — the span of a set of vectors."
