import Game.Metadata
import Game.Levels.Definitions


World "DemoWorld"
Level 1

Title "Exploring the identity and communativity"

Introduction "We are going to begin by looking at the usage of two of our exams to expand them
! The two axioms are add_zero: `∀ a :  F, a + 0 = a` and add_comm : ∀ a b :  F , a + b = b + a.
Using these two axioms we want to expand upon add_zero to be in a more complete. What i mean by this
is that ater this level we will not only be able to say that a + 0 = a, but that 0+a =a."

variable {F : Type*} [MyField F]

open MyField

/--
Theorem stating that adding zero on the left leaves an element unchanged:
`0 + a = a `.
-/
TheoremDoc MyField.zero_add as "zero_add" in "Addition"

Statement MyField.zero_add (x : F): x + 0 = 0 + x := by
  rw [add_comm x 0]   -- rewrites goal to x + 0 = x

Conclusion "Congratulations! You have completed your first level
and can now use the theorem zero_add, you shall see it in theorems on the
next level."

/- Use these commands to add items to the game's inventory. -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq

/--
Theorem stating that adding zero on the right leaves an element unchanged:
`a + 0 = a`.
-/
TheoremDoc MyField.add_zero as "add_zero" in "Addition"

/--
Theorem stating that addition is commutative:
`a + b = b + a`.
-/
TheoremDoc MyField.add_comm as "add_comm" in "Addition"



NewTheorem MyField.add_zero MyField.add_comm
