import Game.Metadata
import Game.Levels.Definitions

World "DemoWorld"
Level 1

Title "Hello World"

Introduction "We are going to begin by looking at the usage of two of our axioms to expand them.
The two axioms are add_zero: ∀ a : F, a + 0 = a and add_comm : ∀ a b : F, a + b = b + a.
Using these two axioms we want to expand upon add_zero to be in a more complete form." 

variable {F : Type*} [MyField F]

Statement (x : F) : x + 0 = 0 + x := by
  rw [MyField.add_zero x]
  rw [MyField.add_comm x 0]
  rw [MyField.add_zero 0]

Conclusion "This last message appears if the level is solved."



