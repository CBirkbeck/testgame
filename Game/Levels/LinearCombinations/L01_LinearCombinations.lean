import Game.Metadata
import Game.Levels.Definitions

World "LinearCombinations"
Level 1

Title "What are Linear Combinations?"
Introduction "Supose that V is a vector space over a field F and that v_1...v_n ∈ V , if α_1...α_n ∈ F we say that the vector
v= α_1v_1...+α_nv_n is a linear combination of the vectors v_1..v_n. Lets explore this through what we have learnt about subspaces! We are going to comsider the subspace where we have three vectors and three vectors and see that a linear combination of them will natturaly lie in the subspace."
variable {F V : Type*} [MyField F] [MyVectorSpace F V]
variable (W : MySubspace F V)

/--
Theorem stating that 3 vectors are closed under linear combinations in a subspace:
`v_1 v_2 v_3 ∈ W → α_1v_1+α_2v_2+α_3v_3 ∈ W`.
-/
TheoremDoc MyLinearCombinations.lin_com3 as "lin_com3" in "LinearCombinations"
Statement MyLinearCombinations.lin_com3 (W : MySubspace F V) (α_1 α_2 α_3 : F) (v_1 v_2 v_3 : V) (hv_1 : v_1 ∈ W) (hv_2 : v_2 ∈ W) (hv_3 : v_3 ∈ W) : (α_1 • v_1 + α_2 • v_2 + α_3 • v_3 ∈ W) := by
exact W.add_mem
    (W.add_mem
      (W.smul_mem hv_1)
      (W.smul_mem hv_2))
    (W.smul_mem hv_3)

Conclusion "well done I hope you see how this is a linear combination, we will next move onto spanning"
