import Game.Metadata
import Game.Levels.Definitions -- this should import Game.Defs.MyField etc.
open Game.Defs MyFieldLemmas

/- Inventory: declare tactics & theorems BEFORE worlds -/
NewTactic rw rfl
TacticDoc rw "The `rw` tactic replaces terms using known equalities."
/- If the game requires theorems to be unlocked, list them: -/
NewTheorem Game.Defs.MyField.add_zero Game.Defs.MyField.add_comm

World "DemoWorld"
Level 1

Title "Hello World"

Introduction "We are going to begin by looking at the usage of two axioms...
The two axioms are add_zero: ∀ a : F, a + 0 = a and add_comm : ∀ a b : F, a + b = b + a."

variable {F : Type*} [Game.Defs.MyField F]

Statement (x : F) : x + 0 = 0 + x := by
  -- rewrite in the order that matches the goal
  rw [Game.Defs.MyField.add_zero x]
  rw [Game.Defs.MyField.add_comm x 0]
  rw [Game.Defs.MyField.add_zero 0]

Conclusion "This last message appears if the level is solved."




