import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.DemoWorld.L02_HelloWorld

World "DemoWorld"
Level 3

Title "Combining multiplication and addition"

Introduction "You have proved both identity theorems. Now combine them.

Your goal is:   x * (0 + y) = (y + 0) * x

Both sides equal x * y, which you can see by applying commutativity of addition
and commutativity of multiplication. In Lean, each step must be explicit.


Always supply explicit arguments to rw when there are multiple subterms that
could match, so Lean rewrites exactly the one you intend."


variable {F : Type*} [MyField F]

Statement (x y : F) : x * (0 + y) = (y + 0) * x := by
  Hint "Apply mul_comm first to swap the factors of multiplication, then add_comm to reorder the sum."
  rw [MyField.mul_comm x (0 + y)]
  rw [MyField.add_comm 0 y]

Conclusion "Great work! You have combined two commutativity axioms in a single proof.
Level 4 is the most challenging in this world.
It introduces three new tactics: rcases, refine, and the backward rewrite ←."
