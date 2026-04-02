import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.SubSpaces.L05_SubSpaces

World "SubSpaces"
Level 6

Title "Intersection of two subspaces ii"

Introduction "In Level 5 we showed U ∩ W contains 0 and is non-empty.
Now we verify closure under the Subspace Test condition for both subspaces.

Your goal is:  u + α • v ∈ W  ∧  u' + α • v' ∈ U

You have four hypotheses:
  hu  : u  ∈ W      hv  : v  ∈ W
  hu' : u' ∈ U      hv' : v' ∈ U

Each part has exactly the same structure as Level 4.
Use constructor to split, then apply the subspace axioms for W and U in turn.
"

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (W : MySubspace F V) (U : MySubspace F V) (α : F) (u v u' v' : V)
    (hu : u ∈ W) (hv : v ∈ W) (hu' : u' ∈ U) (hv' : v' ∈ U) :
    u + α • v ∈ W ∧ u' + α • v' ∈ U := by
  constructor
  exact W.add_mem hu (W.smul_mem hv)
  exact U.add_mem hu' (U.smul_mem hv')

Conclusion "Congratulations — you have completed Subspaces World and the entire LEAN game!

Levels 5 and 6 together constitute a complete Lean proof of Proposition 1.11(i):
the intersection of two subspaces is a subspace.

Across all three worlds you have formally verified:
  Definition 1.1  (field axioms)
  Proposition 1.3 (a + x = b has a solution)
  Definition 1.5  (vector space axioms)
  Theorem 1.6(i)  (cancellation law)
  Definition 1.7  (subspaces)
  Theorem 1.9     (Subspace Test)
  Proposition 1.11(i) (intersection of subspaces)

Well done!"
