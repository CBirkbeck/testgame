import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.DemoWorld.L02_HelloWorld

World "DemoWorld"
Level 3

Title "Combining multiplication and addition"

Introduction "We are now going to look at combining what we have used so far to prove a slightly more
complex statement. We will be combining the fact that `∀ a b : F, a * b = b * a` and `∀ a : F, a + 0 = a`
to prove our statement."

variable {F : Type*} [MyField F]

Statement (x y : F) : x * (0 + y) = (y + 0) * x := by
  rw [MyField.mul_comm x (0 + y)]
  rw [MyField.add_comm 0 y]

Conclusion "Congratulations, you are becoming quite good at using our theorems!"
