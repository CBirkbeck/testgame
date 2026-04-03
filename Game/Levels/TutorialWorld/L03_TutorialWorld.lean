import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.TutorialWorld.L02_TutorialWorld

World "TutorialWorld"
Level 3

Title "Exact Evidence"

Introduction "You are now comfortable with rw. This level introduces a second essential tactic: exact.

  exact term

closes the current goal immediately, provided that term is a proof of exactly the
statement you need to prove.

In this level you are working in a vector space V over a field F, with a subspace W.
You are given two hypotheses in your local context:
  hu : u ∈ W    (a proof that vector u belongs to W)
  hv : v ∈ W    (a proof that vector v belongs to W)

Your goal is:
  v ∈ W

You already have a proof of this — it is the hypothesis hv.
So  exact hv  closes the goal instantly.

Whenever you can spot a proof term in your context (or in the library) that matches
the goal type exactly, exact is the fastest way to close it."

/-- The `exact` tactic closes a goal by providing a direct proof term
whose type matches the goal exactly.
Examples:
  `exact hv`          — closes goal `v ∈ W` when `hv : v ∈ W`
  `exact W.zero_mem`  — closes goal `0 ∈ W` using the zero_mem field of W
  `exact W.add_mem hu hv` — closes `u + v ∈ W` by applying add_mem to hu and hv -/
TacticDoc exact

NewTactic exact

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (W : MySubspace F V) (u v : V) (hu : u ∈ W) (hv : v ∈ W) : v ∈ W := by
  Hint "You already have a proof of v ∈ W in your context — it is called hv.
Try: exact hv"
  exact hv

Conclusion "Perfect! exact is the simplest way to close a goal: just name the proof you already have.

You will use exact constantly throughout the game:
  exact hv              when a hypothesis matches the goal directly
  exact W.zero_mem      when a structure field matches the goal
  exact W.add_mem hu hv when a theorem applied to arguments matches the goal

The next level shows how to combine exact with the third tactic: constructor."
