import CentralConfigurations.Diagrams.AppendixComponents

/-!
# Distinct circle positions in source and appendix components

The mass-center argument in Proposition 4.12 needs at least one circle.
It only needs a circle cover of an isolated ordinary component, so it also
applies to the appendix's greedy groups without identifying their vertex sets.
-/

namespace CentralConfigurations

theorem OneColorLimit.distinct_circle_of_cover {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (hm : AdmissibleMasses mass)
    (s c : Finset (Fin n)) (his : MatrixIsolated q.matrix c)
    (hcover : MatrixCircleCover q.matrix s c) (i : Fin n) (hi : i ∈ s)
    (hic : q.matrix i i = 1) :
    ∃ j ∈ s, q.matrix j j = 1 ∧ q.position i ≠ q.position j := by
  have hip : q.position i ≠ 0 := by simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hic
  by_contra hn
  apply hip
  apply q.coincident_component_circles_zero hm c i (hcover.1 hi) (q.matrix_isolated_force his)
  intro j hj hjp
  have hjc : q.matrix j j = 1 := by simp [OneColorLimit.matrix, OneColorLimit.Incident, hjp]
  have hjs : j ∈ s := hcover.2 j hj (by rw [hjc]; decide)
  by_contra hji
  exact hn ⟨j, hjs, hjc, Ne.symm hji⟩

theorem RemainingCirclesSaturated.group_circle_cover {n : ℕ} {mass : Fin n → ℂ}
    {q : OneColorLimit ℂ n mass} {remaining : Finset (Fin n)}
    (hsat : RemainingCirclesSaturated q.matrix q.matrix_symm remaining)
    (seed : Fin n) (hseed : seed ∈ remaining)
    (hc : ∃ i ∈ appendixGroup q.matrix remaining seed, q.matrix i i = 1) :
    MatrixCircleCover q.matrix (appendixGroup q.matrix remaining seed)
      (ordinaryComponent q.matrix q.matrix_symm seed) := by
  obtain ⟨i, hi, hic⟩ := hc
  refine ⟨appendixGroup_subset_component _ _ _ _, ?_⟩
  intro j hj hjc
  have hjone : q.matrix j j = 1 := (q.matrix_binary j j).resolve_left hjc
  have hsi := (mem_ordinaryComponent _ _ _ _).mp
    (appendixGroup_subset_component q.matrix q.matrix_symm remaining seed hi)
  have hsj := (mem_ordinaryComponent _ _ _ _).mp hj
  exact hsat.group_circle_mem seed hseed i j (hsi.symm.trans hsj) hic hjone hi

theorem OneColorLimit.appendix_component_groups_circle_cover {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (remaining : Finset (Fin n)) :
    RemainingCirclesSaturated q.matrix q.matrix_symm remaining →
    ∀ s ∈ appendixComponentGroups q.matrix remaining,
      (∃ i ∈ s, q.matrix i i = 1) →
      ∃ seed, MatrixCircleCover q.matrix s (ordinaryComponent q.matrix q.matrix_symm seed) := by
  induction remaining using Finset.strongInductionOn with
  | _ remaining ih =>
      intro hsat s hs hc
      rw [appendixComponentGroups] at hs
      split_ifs at hs with h
      · dsimp only at hs
        rcases List.mem_cons.mp hs with heq | hmem
        · subst s
          exact ⟨_, hsat.group_circle_cover _ (Finset.min'_mem remaining h) hc⟩
        · apply ih _ (Finset.sdiff_ssubset
            (appendixGroup_subset_remaining _ _ _ (Finset.min'_mem remaining h))
            (appendixGroup_nonempty _ _ _))
          · exact hsat.remove_group _ (Finset.min'_mem remaining h)
          · exact hmem
          · exact hc
      · simp at hs

theorem OneColorLimit.appendix_component_circle_cover {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (s : Finset (Fin n)) (hs : s ∈ appendixComponents q.matrix)
    (hc : ∃ i ∈ s, q.matrix i i = 1) :
    ∃ seed, MatrixCircleCover q.matrix s (ordinaryComponent q.matrix q.matrix_symm seed) :=
  q.appendix_component_groups_circle_cover Finset.univ (remainingCirclesSaturated_univ _ _)
    s (List.mem_filter.mp hs).1 hc

end CentralConfigurations
