import Game.Metadata
import Game.Levels.Definitions

World "TutorialWorld"
Level 1

Title "Your First Rewrite"

Introduction "Welcome to the Tutorial World!

This world will teach you the three fundamental tactics you need to play this game:
  rw          — rewrite a goal using an equation
  exact       — close a goal with a direct proof term
  constructor — split a conjunction goal into two parts

We start with the simplest tactic: rw (rewrite).

Recall that a field F satisfies the axiom:
  add_zero : ∀ a : F,  a + 0 = a

In Lean, if your goal contains the expression a + 0, you can replace it with a by writing:
  rw [MyField.add_zero]

Lean finds the left-hand side (a + 0) in your goal and replaces it with the right-hand side (a).
After the substitution the goal becomes  a = a, which Lean closes automatically.

Your goal in this level is:
  a + 0 = a

One rewrite is all you need."

/-- The `rw` tactic rewrites the goal using a given theorem or hypothesis.
Writing `rw [h]` finds the left-hand side of `h` in the current goal and
replaces it with the right-hand side.
After the rewrite, if the goal becomes `x = x`, Lean closes it automatically.
Example: if the goal is `a + 0 = a`, then `rw [MyField.add_zero]` solves it. -/
TacticDoc rw

NewTactic rw

variable {F : Type*} [MyField F]

/--
`MyField.add_zero`: The right-hand additive identity axiom.
For any element `a` in a field, `a + 0 = a`.
-/
TheoremDoc MyField.add_zero as "add_zero" in "Tutorial"

Statement (a : F) : a + 0 = a := by
  Hint "Try: rw [MyField.add_zero]
After the rewrite the goal becomes a = a, which Lean closes automatically."
  rw [MyField.add_zero]

Conclusion "Excellent! You used rw for the first time.

Here is what happened step by step:
  1. The goal was  a + 0 = a
  2. rw [MyField.add_zero] replaced  a + 0  with  a
  3. The goal became  a = a, which Lean closes by reflexivity.

The rw tactic is your most versatile tool. It can be used multiple times in a row:
  rw [lemma1]
  rw [lemma2]
or chained together: rw [lemma1, lemma2].
You will use it throughout Field World and Vector Spaces World."

NewTheorem MyField.add_zero
