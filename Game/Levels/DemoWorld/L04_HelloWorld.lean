import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.DemoWorld.L03_HelloWorld

World "DemoWorld"
Level 4

Title "Solution of a + x = b"

Introduction "We now prove the first part of Proposition 1.3 from the course notes:
if a, b ∈ F then ∃ x : F, a + x = b.

The proof exhibits x = ainv + b, where ainv is the additive inverse of a.
Check: a + (ainv + b) = (a + ainv) + b = 0 + b = b.

Three new tactics are used here.

rcases — The tactic rcases is used to break down statements with connectives into components.
  rcases MyField.add_inv a with ⟨ainv, ha_right, ha_left⟩
  gives you:  ainv : F,  ha_right : a + ainv = 0,  ha_left : ainv + a = 0

refine — The tactic refine works in the same way that “suppose” works in a normal proof: we assume something holds in order to continue proving our statement.
  refine ⟨ainv + b, ?_⟩
  changes the goal to: a + (ainv + b) = b

← (backward rewrite) — applies a theorem right-to-left.
  rw [← MyField.add_asoc a ainv b]
  turns a + (ainv + b) into (a + ainv) + b "


TacticDoc rcases "The `rcases` tactic destructs hypotheses, for example existential statements into their components."
TacticDoc refine "The `refine` tactic works like `exact` but allows leaving holes marked with `?_`."
TacticDoc intro "The `intro` tactic introduces hypotheses into context from a goal beginning with `∀` or `→`."

NewTactic rcases refine intro

/--
Every element of a field has an additive inverse:
`∀ a : F, ∃ b : F, a + b = 0 ∧ b + a = 0`.
-/
TheoremDoc MyField.add_inv as "add_inv" in "Fields"

/--
Addition in a field is associative:
`(a + b) + c = a + (b + c)`.
-/
TheoremDoc MyField.add_asoc as "add_asoc" in "Fields"

variable {F : Type*} [MyField F]

Statement (a b : F) : ∃ x : F, (a + x = b) := by
  Hint "Start with: rcases MyField.add_inv a with ⟨ainv, ha_right, ha_left⟩"
  rcases MyField.add_inv a with ⟨ainv, ha_right, ha_left⟩
  Hint "Then: refine ⟨ainv + b, ?_⟩"
  refine ⟨ainv + b, ?_⟩
  Hint "Then use ← add_asoc to regroup, ha_right to cancel, and zero_add to finish."
  rw [← MyField.add_asoc a ainv b]
  rw [ha_right]
  rw [MyField.zero_add]

Conclusion "Congratulations, that was a tricky one! You have now proved the first part of our
proposition. The method you learned will be used in later levels!"

NewTheorem MyField.add_inv MyField.add_asoc
