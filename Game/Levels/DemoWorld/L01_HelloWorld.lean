import Game.Metadata
import Game.Levels.Definitions

World "DemoWorld"
Level 1

Title "Hello World"

Introduction "We are going to begin by looking at the usage of two of our exams to expand them
! The two axioms are add_zero: ∀ a :  F, a + 0 = a and add_comm : ∀ a b :  F , a + b = b + a.
Using these two axioms we want to expand upon add_zero to be in a more complete form." 

variable {F : Type*} [MyField F]

Statement (x: F): a+0=0+a:= by --ok take it from here charlie
  rw [MyField.add_zero a, MyField.add_comm a 0, MyField.add_zero 0]


Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
