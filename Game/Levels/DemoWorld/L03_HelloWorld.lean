import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.DemoWorld.L01_HelloWorld
import Game.Levels.DemoWorld.L02_HelloWorld

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

Statement (x y: F): x*(0+y) = (y+0)*x := by
  rw [MyField.zero_add]
  rw [MyField.add_zero]
  rw [MyField.mul_comm]







Conclusion "Congrtatulations, you are becoming quite good at using our theormes!
"
