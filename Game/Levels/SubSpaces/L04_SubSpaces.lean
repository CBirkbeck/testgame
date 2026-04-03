import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.SubSpaces.L03_SubSpaces
World "SubSpaces"
Level 4

Title "Subspace test"

Introduction "We now look at the Subspace Test (Theorem 1.9 of the course notes).

Your goal is a conjunction:  (u + α • v ∈ W) ∧ (0 ∈ W)

New tactic: constructor
  When the goal is P ∧ Q, constructor splits it into two separate subgoals.
  Prove them in order: first P, then Q."


variable {F V : Type*} [MyField F] [MyVectorSpace F V]
variable (W : MySubspace F V)

Statement (W : MySubspace F V) (α : F) (u v : V) (hv : v ∈ W) (hu : u ∈ W): (u+ α • v ∈ W)∧(0 ∈ W)  := by

  Hint "This level may take some thinking. Use constructor to split the ∧ goal into two parts."
  constructor
  Hint "For the first part, apply our axioms in a chain: add_mem on top of smul_mem."
  exact W.add_mem hu (W.smul_mem hv)
  exact W.zero_mem
Conclusion "Excellent! You have verified the Subspace Test in Lean.
The key technique: chaining theorem applications.
  W.add_mem hu (W.smul_mem hv)
passes the output of smul_mem directly as the second argument of add_mem.
constructor will appear again in Levels 5 and 6."
