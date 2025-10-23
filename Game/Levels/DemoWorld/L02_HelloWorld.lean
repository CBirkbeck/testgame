import Game.Metadata
import Game.Levels.Definitions


World "DemoWorld"
Level 2

Title "Exploring multiplicative inverse and commutatvity "

Introduction "We are now going to look at the usage of two more of our exams to expand them
,mul_one: ∀ a : F , a * 1 = a and mul_comm: ∀ a b : F, a * b = b * a
Using these two axioms we want to expand upon mul_one so that we can state 1*a=a , not just a*1=a."

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
Theorem stating that multiplying by 1 on the right leaves an element unchanged:
`a * 1 = a`.
-/
TheoremDoc MyField.mul_one as "mul_one" in "Multiplication"

NewTheorem MyField.zero_add MyField.mul_one MyField.zero_add
