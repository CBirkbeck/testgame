import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.DemoWorld.L01_HelloWorld

World "DemoWorld"
Level 2

Title "Exploring multiplicative inverse and commutativity"

Introduction "We are now going to look at the usage of two more of our axioms to expand them,
mul_one: `∀ a : F, a * 1 = a` and mul_comm: `∀ a b : F, a * b = b * a`.
Using these two axioms we want to expand upon mul_one so that we can state 1 * a = a, not just a * 1 = a."

variable {F : Type*} [MyField F]

/--
Theorem stating that multiplying 1 on the right leaves an element unchanged:
`a * 1 = a`.
-/
TheoremDoc MyField.mul_one as "mul_one" in "Multiplication"

/--
Theorem stating that multiplication is commutative:
`a * b = b * a`.
-/
TheoremDoc MyField.mul_comm as "mul_comm" in "Multiplication"

/--
Theorem stating that multiplying 1 on the left leaves an element unchanged:
`1 * a = a`.
-/
TheoremDoc MyField.one_mul as "one_mul" in "Multiplication"

Statement MyField.one_mul (x : F) : 1 * x = x := by
  rw [MyField.mul_comm]
  rw [MyField.mul_one]

Conclusion "Congratulations, you are becoming quite good at using our theorems!
You have once again unlocked a new theorem that you shall see available in the next level."

NewTheorem MyField.mul_one MyField.mul_comm MyField.one_mul
