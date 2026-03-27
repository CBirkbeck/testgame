import GameServer
import Std.Tactic    -- ← this makes exact, intro, rw, refine, rcases available
-- import Mathlib.Tactic.Common  -- optional, if you want additional mathlib tactics

/-!
Use this file to add things that should be available in all levels.

For example, this demo imports the mathlib tactics

*Note*: As long as `Game.lean` exists and ends with the `MakeGame` command,
you are completely free how you structure your lean project, this is merely
a suggestion.

*Bug*: However, things are bugged out if the levels of different worlds are imported
in a random order. Therefore, you should keep the structure of one Lean file per world
which imports all its levels.
-/
