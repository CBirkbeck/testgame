import Game.Levels.VectorSpaces.L01_VectorSpaces
import Game.Levels.VectorSpaces.L02_VectorSpaces
import Game.Levels.VectorSpaces.L03_VectorSpaces
import Game.Levels.VectorSpaces.L04_VectorSpaces

World "VectorSpaces"
Title "Vector Spaces"
Prerequisites "DemoWorld"

Introduction "
Welcome to Vector Spaces World!

You have completed Field World and have a solid grasp of the field axioms. We now build
the central object of this module: a vector space.

Let F be a field. A vector space V over F is a set of elements called vectors, equipped
with two operations:
  Vector addition:       + : V × V → V
  Scalar multiplication: · : F × V → V
satisfying ten axioms VS1–VS10 (Definition 1.5 of the course notes).

The axioms VS1–VS5 govern vector addition — they say that (V, +) is an abelian group,
mirroring the additive structure of a field. The axioms VS6–VS10 govern scalar
multiplication — they describe how scalars from F scale vectors in V. Familiar examples
include ℝⁿ for any n, the space of m × n matrices, and spaces of functions.

Our Lean definition is the typeclass MyVectorSpace F V. Scalars are elements of F and
vectors are elements of V; scalar multiplication is written α • v (the bullet symbol).

One important thing to know before you start: when Lean writes v₁ + v₂ + v₃ + v₄ it
means ((v₁ + v₂) + v₃) + v₄. The brackets are invisible but they are always there, and
they matter when applying the rw tactic. If a rewrite does not work, hover over a +
symbol in the interface to reveal the hidden bracket structure.

The four levels are:
  Level 1 — Permuting four vectors: v₁ + v₂ + v₃ + v₄ = v₂ + v₁ + v₄ + v₃
  Level 2 — Distributing a scalar: α • (v₁ + v₂ + v₃ + v₄) = α•v₁ + α•v₂ + α•v₃ + α•v₄
  Level 3 — Combining permutation and scalar distribution in two lines
  Level 4 — Proving the cancellation law: u + v = v → u = 0  (Theorem 1.6(i))
"
