import Game.Metadata
import Game.Levels.Definitions

World "DemoWorld"
Level 1

Title "Exploring the identity and commutativity"

Introduction "We are going to begin by looking at the usage of two of our axioms to expand them!
The two axioms are add_zero: `∀ a : F, a + 0 = a` and add_comm : `∀ a b : F, a + b = b + a`.
Using these two axioms we want to expand upon add_zero to be more complete. What I mean by this
is that after this level we will not only be able to say that a + 0 = a, but that 0 + a = a."

/-- The `rw` tactic rewrites the goal using a given theorem or hypothesis. -/
TacticDoc rw

NewTactic rw

variable {F : Type*} [MyField F]

open MyField

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

/--
Theorem stating that adding zero on the left leaves an element unchanged:
`0 + a = a`.
-/
TheoremDoc MyField.zero_add as "zero_add" in "Addition"

Statement MyField.zero_add (x : F) : 0 + x = x := by
  rw [add_comm 0 x]
  rw [MyField.add_zero]

Conclusion "Congratulations! You have completed your first level
and can now use the theorem zero_add, you shall see it in theorems on the next level."

NewTheorem MyField.add_zero MyField.add_comm MyField.zero_add
