import Game.Metadata
import Game.Levels.Definitions

World "SubSpaces"
Level 1

Title "Exploring Subspaces"

Introduction "We are going to begin by looking at the properties of a subspace.

Suppose V is a vector space over a field F and W is a subset of V.
W is a subspace of V if it is a vector space in its own right, inheriting
vector addition and scalar multiplication from V.

Our Lean definition of a subspace has three fields:
  zero_mem : 0 ∈ W
  add_mem  : u ∈ W → v ∈ W → u + v ∈ W
  smul_mem : v ∈ W → α • v ∈ W

These correspond exactly to the three conditions of the Subspace Test
(Theorem 1.9 in the course notes).

In this level we verify the first condition: the subspace W must contain 0.

New tactic: exact
  exact term  closes a goal when term has exactly the right type.
  Here, W.zero_mem has type 0 ∈ W, which matches the goal directly."

TacticDoc exact "The `exact` tactic closes a goal by providing a direct proof term
whose type matches the goal exactly. For example: `exact W.zero_mem`."

TacticDoc constructor "The `constructor` tactic splits a conjunction goal `P ∧ Q`
into two separate subgoals. Prove them in order: first P, then Q."

NewTactic exact constructor

variable {F V : Type*} [MyField F] [MyVectorSpace F V]
variable (W : MySubspace F V)

/--
`MySubspace.zero_mem`: Every subspace of a vector space contains the zero vector.
If `W` is a subspace of `V` then `0 ∈ W`.
-/
TheoremDoc MySubspace.zero_mem as "zero_mem" in "Subspaces"

/--
`MySubspace.add_mem`: Every subspace is closed under vector addition.
If `u ∈ W` and `v ∈ W` then `u + v ∈ W`.
-/
TheoremDoc MySubspace.add_mem as "add_mem" in "Subspaces"

/--
`MySubspace.smul_mem`: Every subspace is closed under scalar multiplication.
If `v ∈ W` and `α ∈ F` then `α • v ∈ W`.
-/
TheoremDoc MySubspace.smul_mem as "smul_mem" in "Subspaces"

Statement : 0 ∈ W := by
  Hint "W.zero_mem has type 0 ∈ W, which matches the goal exactly.
Try: exact W.zero_mem"
  exact W.zero_mem

Conclusion "Congratulations! You have shown every subspace contains the zero vector.
Remember: a subset without 0 cannot be a subspace.
The exact tactic closes any goal when you can supply a proof term of exactly the right type.
You will use exact in every remaining level of this world."

NewTheorem MySubspace.zero_mem MySubspace.add_mem MySubspace.smul_mem
