import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.VectorSpaces.L02_VectorSpaces

World "VectorSpaces"
Level 4

Title "Cancellation law for vector addition"

Introduction "In this level we prove Theorem 1.6(i) from the course notes:
if u + v = v then u = 0.

The proof follows this chain (where w satisfies v + w = 0):
  u = u + 0 = u + (v + w) = (u + v) + w = v + w = 0

In Lean we build this chain with backward rewrites.
A new tactic appears: intro h
  When the goal is P → Q, intro h brings P into context as hypothesis h.
"

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (u v : V) (α : F) : u + v = v → u = 0 := by
  Hint "After intro h and rcases, rewrite u as u + 0 using ← add_zero,"
  intro h
  rcases MyVectorSpace.add_inv (F := F) (V := V) v with ⟨w, hvright, hvleft⟩
  rw [← MyVectorSpace.add_zero (F := F) (V := V) u]
  rw [← hvright]
  rw [← MyVectorSpace.add_asoc (F := F) (V := V) u v w]
  rw [h]
Conclusion "Superb! You have proved Theorem 1.6(i) — the cancellation law for vectors.
You used intro, rcases, and multiple backward rewrites to encode a standard
mathematical proof step by step in Lean.
You are now ready for Subspaces World."
