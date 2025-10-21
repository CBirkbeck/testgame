import Game.Metadata
import Game.Levels.Definitions


World "DemoWorld"
Level 1

Title "Hello World"

Introduction "We are going to begin by looking at the usage of two of our exams to expand them
! The two axioms are add_zero: ∀ a :  F, a + 0 = a and add_comm : ∀ a b :  F , a + b = b + a.
Using these two axioms we want to expand upon add_zero to be in a more complete"

variable {F : Type*} [MyField F]

Statement (x : F): x + 0 = 0 + x := by
  rw [MyField.add_comm x 0]   -- rewrites goal to x + 0 = x

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
NewTheorem MyField.add_zero MyField.add_comm
