import Game.Metadata
import Game.Levels.Definitions

World "DemoWorld"
Level 1

Title "Hello World"

Introduction "To begin exploring Fields, we must start with what they are! A field is a set 
F together with two binary operations,+: F ⨯ F → F and ∘: F ⨯ F → F such that our Field axioms hold.
To begin with, we will simply state our axioms, but throughout this world we will explore them more,
so do not worry if they apear daunting. 
Informaly, we can view Fields as a set which we can perform adition and multiplication on, with 
inverses. But this will be formaly defined too!" 

variable {F : Type*} [MyField F]

Statement (x y z : F) (h : x = z) : x * y = z * y := by --ok take it from here charlie
  rw [h]

Conclusion "This last message appears if the level is solved."

/- Use these commands to add items to the game's inventory. -/

NewTactic rw rfl
-- NewTheorem Nat.add_comm Nat.add_assoc
-- NewDefinition Nat Add Eq
