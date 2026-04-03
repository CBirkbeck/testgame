import Game.Levels.TutorialWorld.L01_TutorialWorld
import Game.Levels.TutorialWorld.L02_TutorialWorld
import Game.Levels.TutorialWorld.L03_TutorialWorld
import Game.Levels.TutorialWorld.L04_TutorialWorld

World "TutorialWorld"
Title "Tutorial World"

Introduction "
Welcome to the Tutorial World!

Before diving into the mathematics, this world will teach you the three tactics
you will use throughout the entire game:

  rw          Rewrite the goal using an equation.
              rw [MyField.add_zero] finds  a + 0  in your goal and replaces it with  a.

  exact       Close a goal by providing a proof term of exactly the right type.
              exact hv closes the goal  v ∈ W  when you have  hv : v ∈ W  in context.

  constructor Split a conjunction goal  P ∧ Q  into two separate subgoals.
              Prove each one in turn with rw or exact.

No prior knowledge of Lean is assumed. Each level introduces one new idea with
a worked example and a hint to get you started.

The four levels are:
  Level 1 — rw: rewriting with add_zero
  Level 2 — rw: chaining rewrites with add_asoc
  Level 3 — exact: closing a goal from a hypothesis
  Level 4 — constructor: splitting a conjunction and combining all three tactics

Complete all four levels and you will be fully equipped for the worlds ahead.
"
