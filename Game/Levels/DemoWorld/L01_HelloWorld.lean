import Game.Metadata
import Game.Levels.Definitions

World "DemoWorld"
Level 1

Title "Hello World"

Introduction "In this level we are going to begin looking at one of our axioms, the add_zero axiom: ∀ a ∈ F ∃ 0 ∈ F s.t 0+a=a. 
We want to extend it to ∀ a ∈ F ∃ a ∈ F s.t a+0=a=0+a  " 

variable {F : Type*} [MyField F]

Statement (a : F) : a+0 =0+a := by --ok take it from here charlie
  rw [MyField.add_zero a, MyField.add_comm a 0, MyField.add_zero 0]

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
