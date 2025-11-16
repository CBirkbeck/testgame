import Game.Metadata
import Game.Levels.Definitions


World "DemoWorld"
Level 3

Title "combing multiplication and addition"

Introduction "We are now going to look at combining what we have used so far to prove a slightly more
complex statement
-/
/-
We will be looking at combining the fact that
` ∀ a b : F, a * b = b * a`
and
` ∀ a :  F, a + 0 = a`
To prove our statement
"
variable {F : Type*} [MyField F]

Statement (x y: F): x*(0+y) = (0+y)*x := by
  rw [MyField.zero_add]
  rw [MyField.mul_comm x y]

Conclusion "Congrtatulations, you are becoming quite good at using our theormes!
You have once again unlocked a new theorem that you shall see available
in the next level."
