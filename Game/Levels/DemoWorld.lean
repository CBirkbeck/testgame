import Game.Levels.DemoWorld.L01_HelloWorld
import Game.Levels.DemoWorld.L02_HelloWorld
import Game.Levels.DemoWorld.L03_HelloWorld
import Game.Levels.DemoWorld.L04_HelloWorld

World "DemoWorld"
Title "Demo World"

Introduction "
Welcome to Field World!

Before we can study vector spaces, we need to understand the algebraic structure that
underpins all of linear algebra: a field.

A field F = (F, +, ·, 0, 1) is a set together with two binary operations — addition
and multiplication — satisfying eleven axioms. Informally, a field is any set on which
we can add, subtract, multiply and divide in a sensible way. The real numbers ℝ, the
rationals ℚ, the complex numbers ℂ, and the finite fields ℤ/pℤ (for any prime p) are
all familiar examples.

The axioms split into three groups. For addition (A1–A5): closure, additive identity 0,
additive inverses, associativity, commutativity. For multiplication (M1–M5): closure,
multiplicative identity 1, multiplicative inverses for non-zero elements, associativity,
commutativity. And the distributive law D1 linking the two operations.

Our Lean definition captures all of these as the typeclass MyField. You do not need to
memorise every axiom at once — the levels in this world will introduce them one by one.
The only tactic you need to begin with is rw (rewrite). When you write rw [thm], Lean
finds the left-hand side of thm in the current goal and replaces it with the right-hand
side. You will quickly see how powerful this is.

The four levels are:
  Level 1 — Proving 0 + x = x   (left-hand additive identity, derived from axiom A2)
  Level 2 — Proving 1 * x = x   (left-hand multiplicative identity, from axiom M2)
  Level 3 — Combining addition and multiplication commutativity
  Level 4 — Showing the equation a + x = b always has a solution (Proposition 1.3)
"
