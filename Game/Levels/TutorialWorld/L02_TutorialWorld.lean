import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.TutorialWorld.L01_TutorialWorld

World "TutorialWorld"
Level 2

Title "Chaining Rewrites"

Introduction "Well done on completing Level 1!

You know that rw replaces a subexpression using an equation.
In this level you will need to apply rw twice, using two different field axioms.

Recall:
  add_comm  : ∀ a b : F,  a + b = b + a
  mul_comm  : ∀ a b : F,  a * b = b * a

Your goal is:
  a + b * c = b * a + a


Hint: try both rewrites in this order:
  rw [MyField.mul_comm c a]   — this targets c * a if it appears; be precise!
  rw [MyField.add_comm]

The explicit form  rw [MyField.add_comm a b]  tells Lean exactly which pair to swap."

variable {F : Type*} [MyField F]

/--
`MyField.add_comm`: Addition in a field is commutative.
For any `a b : F`, `a + b = b + a`.
-/
TheoremDoc MyField.add_comm as "add_comm" in "Tutorial"

/--
`MyField.mul_comm`: Multiplication in a field is commutative.
For any `a b : F`, `a * b = b * a`.
-/
TheoremDoc MyField.mul_comm as "mul_comm" in "Tutorial"

Statement (a b c : F) : (a + b) + c = a + (b + c) := by
  Hint "This is the associativity axiom add_asoc. Try: rw [MyField.add_asoc]"
  rw [MyField.add_asoc]

Conclusion "You used rw with the associativity axiom.

Key lesson: rw [lemma] rewrites the *first* matching subterm it finds.
If a lemma has free variables — like  add_asoc a b c — Lean infers them from the goal.
You can also write  rw [MyField.add_asoc a b c]  to be explicit.

In longer proofs you will chain several rw steps. Try writing each one on its own line
so you can see the intermediate goals change in the info panel."

NewTheorem MyField.add_comm MyField.mul_comm MyField.add_asoc
