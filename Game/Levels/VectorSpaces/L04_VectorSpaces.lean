import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.VectorSpaces.L02_VectorSpaces

World "VectorSpaces"
Level 4

Title "Cancellation law for vector addition"

Introduction "In this level we prove that if u + v = v then u must be the zero vector.
This is the cancellation law, and uses the existence of additive inverses."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (u v : V) (α : F) : u + v = v → u = 0 := by
  intro h
  rcases MyVectorSpace.add_inv (F := F) (V := V) v with ⟨w, hvright, hvleft⟩
  rw [← MyVectorSpace.add_zero (F := F) (V := V) u]
  rw [← hvright]
  rw [← MyVectorSpace.add_asoc (F := F) (V := V) u v w]
  rw [h]import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.VectorSpaces.L02_VectorSpaces

World "VectorSpaces"
Level 4

Title "Cancellation law for vector addition"

Introduction "In this level we prove that if u + v = v then u must be the zero vector.
This is the cancellation law, and uses the existence of additive inverses."

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (u v : V) (α : F) : u + v = v → u = 0 := by
  intro h
  rcases MyVectorSpace.add_inv (F := F) (V := V) v with ⟨w, hvright, hvleft⟩
  rw [← MyVectorSpace.add_zero (F := F) (V := V) u]
  rw [← hvright]
  rw [← MyVectorSpace.add_asoc (F := F) (V := V) u v w]
  rw [h]
