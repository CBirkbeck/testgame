import Game.Metadata
import Game.Levels.Definitions

World "DemoWorld"
Level 1

Title "Hello World"

Introduction "This text is shown as first message when the level is played.
You can insert hints in the proof below. They will appear in this side panel
depending on the proof a user provides."

variable {F : Type*} [MyField F]

Statement (x y z : F) (h : x = z) : x * y = z * y := by --ok take it from here charlie
  rw [h]

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
