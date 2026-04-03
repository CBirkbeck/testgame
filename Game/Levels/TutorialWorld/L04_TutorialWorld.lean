import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.TutorialWorld.L03_TutorialWorld

World "TutorialWorld"
Level 4

Title "Splitting Goals with Constructor"

Introduction "You have now seen rw and exact in action.
This final tutorial level introduces the third core tactic: constructor.

  constructor

When your goal is a conjunction  P ∧ Q  (read: 'P and Q'), you cannot prove it in one shot.
constructor splits it into two separate subgoals:
  Subgoal 1: prove P
  Subgoal 2: prove Q

You prove them one after the other.

In this level you are working in a vector space V over a field F, with a subspace W.
You are given:
  hu : u ∈ W
  hv : v ∈ W

Your goal is:
  (0 ∈ W) ∧ (u + v ∈ W)

Steps:
  1. constructor            — splits into two subgoals
  2. exact W.zero_mem       — every subspace contains 0; closes the first subgoal
  3. exact W.add_mem hu hv  — closure under addition; closes the second subgoal

The subspace axioms W.zero_mem and W.add_mem are previewed here so you can see them
in action — they will be studied in full detail in Subspaces World."

/-- The `constructor` tactic splits a conjunction goal `P ∧ Q`
into two separate subgoals. Prove them in order:
  constructor
  · -- prove P
  · -- prove Q
You can omit the bullet points; Lean processes the subgoals sequentially. -/
TacticDoc constructor

NewTactic constructor

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (W : MySubspace F V) (u v : V) (hu : u ∈ W) (hv : v ∈ W) :
    (0 ∈ W) ∧ (u + v ∈ W) := by
  Hint "The goal is a conjunction. Use constructor to split it into two parts."
  constructor
  Hint "First subgoal: 0 ∈ W. Every subspace contains 0. Try: exact W.zero_mem"
  exact W.zero_mem
  Hint "Second subgoal: u + v ∈ W. Apply add_mem to your hypotheses.
Try: exact W.add_mem hu hv"
  exact W.add_mem hu hv

Conclusion "Outstanding! You have now mastered all three tutorial tactics:

  rw [lemma]   — rewrite the goal using an equation
  exact term   — close the goal with a matching proof term
  constructor  — split a conjunction P ∧ Q into two subgoals

These three tactics, combined with the field, vector space, and subspace axioms,
are enough to complete every level in this game.

You are ready to begin Field World. Good luck!"
