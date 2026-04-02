import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.DemoWorld.L01_HelloWorld

World "DemoWorld"
Level 2

Title "Exploring multiplicative inverse and commutativity"

Introduction "In Level 1 you used commutativity of addition to derive the left-hand additive identity.
Now do exactly the same for multiplication.

The axiom mul_one states:    ∀ a : F, a * 1 = a
The axiom mul_comm states:   ∀ a b : F, a * b = b * a

Your goal is to prove 1 * x = x.
The proof has exactly the same two-step structure as Level 1

Notice: the additive and multiplicative structures of a field are both abelian groups,
so the same proof pattern works for both."


variable {F : Type*} [MyField F]

/--
Theorem stating that multiplying 1 on the right leaves an element unchanged:
`a * 1 = a`.
-/
TheoremDoc MyField.mul_one as "mul_one" in "Fields"

/--
Theorem stating that multiplication is commutative:
`a * b = b * a`.
-/
TheoremDoc MyField.mul_comm as "mul_comm" in "Fields"

/--
Theorem stating that multiplying 1 on the left leaves an element unchanged:
`1 * a = a`.
-/
TheoremDoc MyField.one_mul as "one_mul" in "Fields"

Statement MyField.one_mul (x : F) : 1 * x = x := by
  Hint "The proof is identical in structure to Level 1. Try rw [MyField.mul_comm] first."
  rw [MyField.mul_comm]
  rw [MyField.mul_one]

Conclusion "Well done! You have proved one_mul — the left-hand multiplicative identity.
You now have both identity theorems available.
Level 3 combines commutativity of addition and multiplication in a single proof."


NewTheorem MyField.mul_one MyField.mul_comm MyField.one_mul
