import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.TutorialWorld.L01_TutorialWorld

World "TutorialWorld"
Level 2

Title "Chaining Rewrites"

Introduction "Well done on completing Level 1!


Recall the associativity axiom:
  add_asoc : ∀ a b c : F,  (a + b) + c = a + (b + c)

Your goal is:
  (a + b) + c = a + (b + c)

This matches the left-hand side of add_asoc exactly.
A single rw [MyField.add_asoc] rewrites it to  a + (b + c) = a + (b + c),
which Lean closes automatically.


In later levels you will chain several rw steps to rearrange longer expressions.
Each rw changes the goal and you can watch it update in the info panel on the right."

/--
`MyField.add_asoc`: Addition in a field is associative.
For any `a b c : F`, `(a + b) + c = a + (b + c)`.
-/
TheoremDoc MyField.add_asoc as "add_asoc" in "Tutorial"

NewTheorem MyField.add_asoc

variable {F : Type*} [MyField F]

Statement (a b c : F) : (a + b) + c = a + (b + c) := by
  Hint "This is the associativity axiom. Try: rw [MyField.add_asoc]"
  rw [MyField.add_asoc]

Conclusion "You used rw with the associativity axiom.

Key lesson: rw [lemma] rewrites the *first* matching subterm it finds.
If a lemma has free variables — like  add_asoc a b c — Lean infers them from the goal.
You can also write  rw [MyField.add_asoc a b c]  to target a specific occurrence.

In longer proofs you will chain several rw steps. Try writing each one on its own line
so you can see the intermediate goals change in the info panel."
