import Game.Metadata
import Game.Levels.Definitions
import Game.Levels.TutorialWorld.L02_TutorialWorld

World "TutorialWorld"
Level 3

Title "Exact Evidence"

Introduction "You are now comfortable with rw. This level introduces a second essential tactic: exact.

  exact term

closes the current goal immediately, provided that term has exactly the right type
(i.e. it is a proof of exactly the statement you need to prove).

In this level you are given hypotheses — named proof terms that live in your local context.
Look at the goal and ask yourself: do I already have a proof of this?

You are working in a vector space V over a field F.
You are given:
  hv : v ∈ W    (a proof that the vector v belongs to subspace W)
  hu : u ∈ W    (a proof that the vector u belongs to subspace W)

Your goal is:
  v ∈ W

You already have a proof of v ∈ W — it is called hv.
So  exact hv  closes the goal instantly.

New tactic: exact
  exact term  closes a goal when term has exactly the type you need to prove.
  Here, hv has type v ∈ W, which matches the goal, so exact hv works."

TacticDoc exact "The `exact` tactic closes a goal by providing a direct proof term
whose type matches the goal exactly.
Examples:
  exact hv         — closes goal  v ∈ W  when  hv : v ∈ W
  exact W.zero_mem — closes goal  0 ∈ W  using the zero_mem field of the subspace W
  exact W.add_mem hu hv — closes  u + v ∈ W  by applying add_mem to hu and hv"

NewTactic exact

variable {F V : Type*} [MyField F] [MyVectorSpace F V]

Statement (W : MySubspace F V) (u v : V) (hu : u ∈ W) (hv : v ∈ W) : v ∈ W := by
  Hint "You already have a proof of v ∈ W in your context. It is called hv.
Try: exact hv"
  exact hv

Conclusion "Perfect! exact is the simplest way to close a goal: just name the proof you already have.

You will use exact constantly:
  — exact hv           when a hypothesis matches the goal directly
  — exact W.zero_mem   when a theorem or structure field matches the goal
  — exact W.add_mem hu hv  when a theorem applied to arguments matches the goal

The next level shows how exact and rw can be combined, and introduces the third
tactic: constructor."
