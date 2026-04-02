import Game.Metadata
import Game.Levels.Definitions

World "DemoWorld"
Level 1

Title "Exploring the identity and commutativity"

Introduction "We are going to begin by looking at two of our axioms.
The axiom add_zero states:   ∀ a : F, a + 0 = a
The axiom add_comm states:   ∀ a b : F, a + b = b + a

Our field definition only gives the right-hand additive identity (a + 0 = a),
but Axiom A2 in the course notes requires both sides: 0 + a = a = a + 0.
In this level we derive the left-hand version 0 + x = x from these two axioms.

The only tactic you need is rw (rewrite).
rw [thm] finds the left-hand side of thm in the goal and replaces it with the right-hand side.

Step 1: rw [add_comm 0 x]   — rewrites 0 + x  to  x + 0.
Step 2: rw [MyField.add_zero]   — rewrites x + 0  to  x, closing the goal."


/-- The `rw` tactic rewrites the goal using a given theorem or hypothesis. -/
TacticDoc rw

NewTactic rw

variable {F : Type*} [MyField F]

open MyField

/--
Theorem stating that adding zero on the right leaves an element unchanged:
`a + 0 = a`.
-/
TheoremDoc MyField.add_zero as "add_zero" in "Fields"

/--
Theorem stating that addition is commutative:
`a + b = b + a`.
-/
TheoremDoc MyField.add_comm as "add_comm" in "Fields"

/--
Theorem stating that adding zero on the left leaves an element unchanged:
`0 + a = a`.
-/
TheoremDoc MyField.zero_add as "zero_add" in "Fields"

Statement MyField.zero_add (x : F) : 0 + x = x := by
  rw [add_comm 0 x]
  rw [MyField.add_zero]

Conclusion "Congratulations! You have proved zero_add — the left-hand additive identity.
You derived it from the right-hand identity and commutativity, with no extra axiom needed.
The theorem zero_add is now unlocked and available in all future levels."


NewTheorem MyField.add_zero MyField.add_comm MyField.zero_add
