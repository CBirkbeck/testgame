import Game.Metadata
import Game.Levels.Definitions


World "DemoWorld"
Level 3

Title "combing multiplication and addition"

Introduction "We are now going to look at combining what we have used so far to prove a slightly more
complex statement"

variable {F : Type*} [MyField F]

Statement (x : F): x*1 = 1*x := by
  rw [MyField.mul_comm]

Conclusion "Congrtatulations, you are becoming quite good at using our theormes!
You have once again unlocked a new theorem that you shall see available
in the next level."

/--
Theorem stating that adding zero on the left leaves an element unchanged:
`0 + a = a `.
-/
TheoremDoc MyField.zero_add as "zero_add" in "Addition"
/--
Theorem stating that multiplyig 1 on the right leaves an element unchanged:
`a * 1 = a`.
-/

TheoremDoc MyField.mul_one as "mul_one" in "Multiplication"

/--
Theorem stating that multiplying on the right side is the same as the left side:
`a * b = b * a`.
-/
TheoremDoc MyField.mul_comm as "mul_comm" in "Multiplication"

NewTheorem MyField.zero_add MyField.mul_one MyField.mul_comm
