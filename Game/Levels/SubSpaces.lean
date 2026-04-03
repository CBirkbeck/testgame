import Game.Levels.SubSpaces.L01_SubSpaces
import Game.Levels.SubSpaces.L02_SubSpaces
import Game.Levels.SubSpaces.L03_SubSpaces
import Game.Levels.SubSpaces.L04_SubSpaces
import Game.Levels.SubSpaces.L05_SubSpaces
import Game.Levels.SubSpaces.L06_SubSpaces

World "SubSpaces"
Title "Sub Spaces"


Introduction "
Welcome to Subspaces World!

You have now mastered both fields and vector spaces. In this world we turn to subspaces —
special subsets of a vector space that are vector spaces in their own right.

Recall Definition 1.7 from the course notes: suppose V is a vector space over a field F
and W is a subset of V. We say that W is a (vector) subspace of V if it is a vector space
in its own right with respect to the vector addition and scalar multiplication inherited
from V.

Checking all ten vector space axioms for a subset would be very tedious. Thankfully,
Lemma 1.8 tells us that any subset automatically inherits VS4, VS5, VS7, VS8, VS9 and
VS10 from V. So we only need to check four things. In fact, the Subspace Test
(Theorem 1.9) reduces this further to just three conditions:

  (i)   W ≠ ∅, equivalently 0 ∈ W
  (ii)  u, v ∈ W ⟹ u + v ∈ W          (closed under addition)
  (iii) v ∈ W, λ ∈ F ⟹ λv ∈ W         (closed under scalar multiplication)

Our Lean definition encodes exactly these three conditions as fields of the MySubspace
structure:
  zero_mem : 0 ∈ carrier
  add_mem  : u ∈ W → v ∈ W → u + v ∈ W
  smul_mem : v ∈ W → α • v ∈ W

The proofs in this world are generally short — the mathematical content comes from
understanding why each condition matters, not from long tactic sequences. The two tactics
you will use throughout are exact (to close a goal with a matching proof term) and
constructor (to split a conjunction P ∧ Q into two subgoals).

The six levels are:
  Level 1 — Every subspace contains 0                     (zero_mem)
  Level 2 — Closed under addition                         (add_mem)
  Level 3 — Closed under scalar multiplication            (smul_mem)
  Level 4 — The full Subspace Test: u + α • v ∈ W        (Theorem 1.9)
  Level 5 — Intersection of subspaces, part I: 0 ∈ U ∩ W
  Level 6 — Intersection of subspaces, part II: closure   (Proposition 1.11(i))
"
