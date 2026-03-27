import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.DemoWorld.L03_HelloWorld

World "DemoWorld"
Level 4

Title "Solution of a + x = b"

Introduction "We are now going to look at using what we have learned about fields to show one of their
applied properties. We will be proving that if a, b ∈ F then a + x = b has a solution of the form
x = ainv + b. HINT: start by writing `rcases MyField.add_inv a with ⟨ainv, ha_right, ha_left⟩`"

NewTactic rcases refine intro

/--
Every element of a field has an additive inverse:
`∀ a : F, ∃ b : F, a + b = 0 ∧ b + a = 0`.
-/
TheoremDoc MyField.add_inv as "add_inv" in "Addition"

/--
Addition in a field is associative:
`(a + b) + c = a + (b + c)`.
-/
TheoremDoc MyField.add_asoc as "add_asoc" in "Addition"

variable {F : Type*} [MyField F]

Statement (a b : F) : ∃ x : F, (a + x = b) := by
  rcases MyField.add_inv a with ⟨ainv, ha_right, ha_left⟩
  refine ⟨ainv + b, ?_⟩
  rw [← MyField.add_asoc a ainv b]
  rw [ha_right]
  rw [MyField.zero_add]

Conclusion "Congratulations, that was a tricky one! You have now proved the first part of our
proposition. The method you learned will be used in later levels!"

NewTheorem MyField.add_inv MyField.add_asoc
