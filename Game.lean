import Game.Levels.TutorialWorld
import Game.Levels.DemoWorld
import Game.Levels.VectorSpaces
import Game.Levels.LinearCombinations
import Game.Levels.SubSpaces

Title "Linear Algebra LEAN Game"

Introduction "Welcome to the Linear Algebra LEAN Game!
This game is based on the second-year UEA module Complex Functions and Linear Algebra,
supervised by Christopher Birkbeck.

There are five worlds to complete, each building on the last.
Complete them in order — each world unlocks the next.

  Tutorial World      — Learn the three core tactics: rw, exact, constructor
  Field World         — Explore the axioms of a field (Definition 1.1)
  Vector Spaces World — Build intuition for vector space axioms (Definition 1.5)
  Linear Combinations — Reason about linear combinations of vectors
  Subspaces World     — Prove the Subspace Test (Theorem 1.9)

Start with Tutorial World if you are new to Lean."

Info "Created by Charlie Yates as part of dissertation MTHA7029Y
at the University of East Anglia.
The mathematics covers fields (Definition 1.1), vector spaces (Definition 1.5),
linear combinations, and subspaces (Definition 1.7, Theorem 1.9)."

Languages "en"
CaptionShort "Linear Algebra LEAN Game"
CaptionLong "A Lean 4 game teaching fields, vector spaces, linear combinations and subspaces from the UEA second-year linear algebra module."

MakeGame
