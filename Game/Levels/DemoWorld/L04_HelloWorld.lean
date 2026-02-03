import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.DemoWorld.L03_HelloWorld


World "DemoWorld"
Level 4
Title "solution of a+x=b"

Introduction "We are now going to look at using what we have learned about fields to show one of their aplied properties.
-/
/-
We will be looking at proving that if a,b ∈ F then a+x=b has a solution of the form x = ainv + b (HINT start by writing 'rcases MyField.add_inv a with ⟨ainv, ha_right, ha_left⟩' )
"

variable {F : Type*} [MyField F]

Statement (a b  : F) : ∃ x : F ,  (a + x = b ) := by

  rcases MyField.add_inv a with ⟨ainv, ha_right, ha_left⟩
  refine ⟨ainv + b, ?_⟩
  rw [← MyField.add_asoc a ainv b]
  rw [ha_right]
  rw [MyField.zero_add]

Conclusion "Congrtatulations, that was a tricky one, but the method you learned will be used in later levels! you have now proved the first part of our proposition and the final level of this world will be proving the second condition.
"
