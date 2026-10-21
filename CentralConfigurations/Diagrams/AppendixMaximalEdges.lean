import CentralConfigurations.Diagrams.ComponentCirclePairs
import CentralConfigurations.Diagrams.SourceMaximalEdges
import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp

/-!
# Maximal-stroke retention in Appendix I/II component groups

The greedy groups use A^(n-1), not ordinary connectivity. A component whose
circles remain has not yet lost any vertex. Two circles provide enough
path-length slack to retain each circle's neighbors at the fixed exponent.
This supplies the additional bridge needed by Proposition 4.8.
-/

namespace CentralConfigurations

open scoped BigOperators

theorem integerMatrix_pow_concat_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (i r j : Fin n) (k m : ℕ) (hk : 0 < (integerMatrix A ^ k) i r)
    (hm : 0 < (integerMatrix A ^ m) r j) : 0 < (integerMatrix A ^ (k + m)) i j := by
  rw [pow_add, Matrix.mul_apply]
  exact (mul_pos hk hm).trans_le (Finset.single_le_sum
    (fun v _ => mul_nonneg (integerMatrix_pow_nonneg A k i v)
      (integerMatrix_pow_nonneg A m v j)) (Finset.mem_univ r))

theorem walk_loop_padding_power_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) {i j : Fin n}
    (p : (offDiagonalGraph A hs).Walk i j) (r : Fin n) (hr : r ∈ p.support)
    (hrr : A r r = 1) (k : ℕ) (hk : p.length ≤ k) :
    0 < (integerMatrix A ^ k) i j := by
  have hlength : (p.takeUntil r hr).length + (p.dropUntil r hr).length = p.length := by
    simpa only [SimpleGraph.Walk.length_append] using congrArg SimpleGraph.Walk.length (p.take_spec hr)
  have hleft : 0 < (integerMatrix A ^ (k - (p.dropUntil r hr).length)) i r :=
    (walk_integerMatrix_pow_pos A hs (p.takeUntil r hr)).trans_le
      (integerMatrix_pow_le_of_loop A i r hrr (by omega))
  have h := integerMatrix_pow_concat_pos A i r j
    (k - (p.dropUntil r hr).length) (p.dropUntil r hr).length hleft
    (walk_integerMatrix_pow_pos A hs (p.dropUntil r hr))
  simpa only [Nat.sub_add_cancel (by omega : (p.dropUntil r hr).length ≤ k)] using h

theorem loop_neighbor_return_power_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (i j : Fin n) (hii : A i i = 1)
    (hij : A i j = 1) (k : ℕ) (hk : 2 ≤ k) :
    0 < (integerMatrix A ^ k) j j := by
  have heij : 0 < (integerMatrix A ^ 1) i j := by simp [integerMatrix, hij]
  have heji : 0 < (integerMatrix A ^ 1) j i := by simp [integerMatrix, hs j i, hij]
  have heii : 0 < (integerMatrix A ^ 1) i i := by simp [integerMatrix, hii]
  have htwo : 0 < (integerMatrix A ^ 2) j j :=
    integerMatrix_pow_concat_pos A j i j 1 1 heji heij
  have hthree : 0 < (integerMatrix A ^ 3) j j :=
    integerMatrix_pow_concat_pos A j i j 2 1
      (integerMatrix_pow_concat_pos A j i i 1 1 heji heii) heij
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases h2 : k = 2
      · simpa only [h2] using htwo
      by_cases h3 : k = 3
      · simpa only [h3] using hthree
      have hprev := ih (k - 2) (by omega) (by omega)
      have h := integerMatrix_pow_concat_pos A j j j (k - 2) 2 hprev htwo
      simpa only [Nat.sub_add_cancel (by omega : 2 ≤ k)] using h

/-- Two loops anywhere in the finite graph supply the path slack; reachability
is needed from the seed to the neighbor under consideration. -/
theorem reachable_circle_neighbor_power_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (seed i j r : Fin n)
    (hreach : (offDiagonalGraph A hs).Reachable seed j)
    (hii : A i i = 1) (hrr : A r r = 1) (hir : i ≠ r) (he : A i j = 1) :
    0 < (integerMatrix A ^ (n - 1)) seed j := by
  obtain ⟨p, hp⟩ := hreach.exists_isPath
  have hlen : p.length < n := by simpa using hp.length_lt
  by_cases hc : ∃ u ∈ p.support, A u u = 1
  · obtain ⟨u, hu, huu⟩ := hc
    exact walk_loop_padding_power_pos A hs p u hu huu (n - 1) (by omega)
  · have hi : i ∉ p.support.toFinset := by
      intro h
      exact hc ⟨i, List.mem_toFinset.mp h, hii⟩
    have hr : r ∉ p.support.toFinset := by
      intro h
      exact hc ⟨r, List.mem_toFinset.mp h, hrr⟩
    have hic : i ∉ insert r p.support.toFinset := by simp [hir, hi]
    have hcard := Finset.card_le_univ (insert i (insert r p.support.toFinset))
    rw [Finset.card_insert_of_notMem hic, Finset.card_insert_of_notMem hr,
      List.toFinset_card_of_nodup hp.support_nodup, p.length_support] at hcard
    simp only [Fintype.card_fin] at hcard
    have hreturn := loop_neighbor_return_power_pos A hs i j hii he (n - 1 - p.length) (by omega)
    have h := integerMatrix_pow_concat_pos A seed j j p.length (n - 1 - p.length)
      (walk_integerMatrix_pow_pos A hs p) hreturn
    simpa only [Nat.add_sub_of_le (by omega : p.length ≤ n - 1)] using h

/-- If a component still has any circle, all its vertices are still present. -/
def RemainingCircleComponentsComplete {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (remaining : Finset (Fin n)) : Prop :=
  ∀ i ∈ remaining, A i i = 1 → ∀ j, (offDiagonalGraph A hs).Reachable i j → j ∈ remaining

theorem remainingCircleComponentsComplete_univ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) : RemainingCircleComponentsComplete A hs Finset.univ := by
  intro i _ _ j _
  exact Finset.mem_univ j

theorem RemainingCircleComponentsComplete.remove_group {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℕ} {hs : ∀ i j, A i j = A j i}
    {remaining : Finset (Fin n)} (h : RemainingCircleComponentsComplete A hs remaining)
    (seed : Fin n) (_hseed : seed ∈ remaining) :
    RemainingCircleComponentsComplete A hs (remaining \ appendixGroup A remaining seed) := by
  intro i hi hii j hij
  have hi' := Finset.mem_sdiff.mp hi
  apply Finset.mem_sdiff.mpr
  refine ⟨h i hi'.1 hii j hij, ?_⟩
  intro hjg
  have hsj := (mem_ordinaryComponent _ _ _ _).mp
    (appendixGroup_subset_component A hs remaining seed hjg)
  exact hi'.2 (circle_mem_appendixGroup A hs remaining seed i (hsj.trans hij.symm) hii hi'.1)

theorem RemainingCircleComponentsComplete.circles_saturated {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℕ} {hs : ∀ i j, A i j = A j i}
    {remaining : Finset (Fin n)} (h : RemainingCircleComponentsComplete A hs remaining) :
    RemainingCirclesSaturated A hs remaining := by
  intro i j hij hii hjj
  exact ⟨fun hi => h i hi hii j hij, fun hj => h j hj hjj i hij.symm⟩

theorem OneColorLimit.appendix_group_circle_neighbor_mem {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (hm : AdmissibleMasses mass)
    (remaining : Finset (Fin n))
    (hcomplete : RemainingCircleComponentsComplete q.matrix q.matrix_symm remaining)
    (seed : Fin n) (hseed : seed ∈ remaining)
    (hc : ∃ u ∈ appendixGroup q.matrix remaining seed, q.matrix u u = 1)
    (i : Fin n) (hi : i ∈ ordinaryComponent q.matrix q.matrix_symm seed)
    (hic : q.matrix i i = 1) (j : Fin n) (hf : q.force i j ≠ 0) :
    i ∈ appendixGroup q.matrix remaining seed ∧ j ∈ appendixGroup q.matrix remaining seed := by
  have hcover := hcomplete.circles_saturated.group_circle_cover seed hseed hc
  have hig : i ∈ appendixGroup q.matrix remaining seed := hcover.2 i hi (by rw [hic]; decide)
  obtain ⟨r, hr, hrr, hpos⟩ := q.distinct_circle_of_cover hm _ _
    (ordinaryComponent_isolated q.matrix q.matrix_symm seed) hcover i hig hic
  have hir : i ≠ r := fun h => hpos (congrArg q.position h)
  have hij : i ≠ j := by intro h; subst j; exact hf (q.diagonal i)
  have he : q.matrix i j = 1 := by simp [OneColorLimit.matrix, OneColorLimit.Incident, hij, hf]
  have hrj := matrix_entry_reachable q.matrix q.matrix_symm i j (by rw [he]; decide)
  have hreach := ((mem_ordinaryComponent _ _ _ _).mp hi).trans hrj
  have hir' := appendixGroup_subset_remaining q.matrix remaining seed hseed hig
  have hjr := hcomplete i hir' hic j hrj
  refine ⟨hig, Finset.mem_insert_of_mem ?_⟩
  exact Finset.mem_filter.mpr ⟨hjr,
    reachable_circle_neighbor_power_pos q.matrix q.matrix_symm seed i j r hreach hic hrr hir he⟩

theorem OneColorLimit.appendix_group_exists_maximal_stroke {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (hm : AdmissibleMasses mass)
    (remaining : Finset (Fin n))
    (hcomplete : RemainingCircleComponentsComplete q.matrix q.matrix_symm remaining)
    (seed : Fin n) (hseed : seed ∈ remaining)
    (hc : ∃ u ∈ appendixGroup q.matrix remaining seed, q.matrix u u = 1) :
    ∃ i ∈ appendixGroup q.matrix remaining seed, ∃ j ∈ appendixGroup q.matrix remaining seed,
      q.force i j ≠ 0 ∧ q.position i ≠ q.position j := by
  let c := ordinaryComponent q.matrix q.matrix_symm seed
  have hclosed := q.matrix_isolated_force (ordinaryComponent_isolated q.matrix q.matrix_symm seed)
  have hcircle : ∃ u ∈ c, q.position u ≠ 0 := by
    obtain ⟨u, hu, huc⟩ := hc
    exact ⟨u, appendixGroup_subset_component _ _ _ _ hu,
      by simpa [OneColorLimit.matrix, OneColorLimit.Incident] using huc⟩
  obtain ⟨i, hi, j, hj, hf, hpos⟩ := (q.component_maximal_iff_circle hm c hclosed).mpr hcircle
  by_cases hpi : q.position i = 0
  · have hpj : q.position j ≠ 0 := by intro h; exact hpos (hpi.trans h.symm)
    have hji : q.force j i ≠ 0 := by rw [q.antisymm j i]; exact neg_ne_zero.mpr hf
    have hcj : q.matrix j j = 1 := by simp [OneColorLimit.matrix, OneColorLimit.Incident, hpj]
    obtain ⟨hjg, hig⟩ := q.appendix_group_circle_neighbor_mem hm remaining hcomplete seed hseed hc j hj hcj i hji
    exact ⟨i, hig, j, hjg, hf, hpos⟩
  · have hci : q.matrix i i = 1 := by simp [OneColorLimit.matrix, OneColorLimit.Incident, hpi]
    obtain ⟨hig, hjg⟩ := q.appendix_group_circle_neighbor_mem hm remaining hcomplete seed hseed hc i hi hci j hf
    exact ⟨i, hig, j, hjg, hf, hpos⟩

theorem OneColorLimit.appendix_groups_maximal_stroke {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (hm : AdmissibleMasses mass) (remaining : Finset (Fin n)) :
    RemainingCircleComponentsComplete q.matrix q.matrix_symm remaining →
    ∀ s ∈ appendixComponentGroups q.matrix remaining, (∃ i ∈ s, q.matrix i i = 1) →
      ∃ i ∈ s, ∃ j ∈ s, q.force i j ≠ 0 ∧ q.position i ≠ q.position j := by
  induction remaining using Finset.strongInductionOn with
  | _ remaining ih =>
      intro hc s hs hcircle
      rw [appendixComponentGroups] at hs
      split_ifs at hs with h
      · dsimp only at hs
        rcases List.mem_cons.mp hs with heq | hmem
        · subst s
          exact q.appendix_group_exists_maximal_stroke hm remaining hc _ (Finset.min'_mem remaining h) hcircle
        · apply ih _ (Finset.sdiff_ssubset
            (appendixGroup_subset_remaining _ _ _ (Finset.min'_mem remaining h))
            (appendixGroup_nonempty _ _ _))
          · exact hc.remove_group _ (Finset.min'_mem remaining h)
          · exact hmem
          · exact hcircle
      · simp at hs

theorem OneColorLimit.appendix_component_exists_maximal_stroke {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (hm : AdmissibleMasses mass) (s : Finset (Fin n))
    (hs : s ∈ appendixComponents q.matrix) (hc : ∃ i ∈ s, q.matrix i i = 1) :
    ∃ i ∈ s, ∃ j ∈ s, q.force i j ≠ 0 ∧ q.position i ≠ q.position j :=
  q.appendix_groups_maximal_stroke hm Finset.univ (remainingCircleComponentsComplete_univ _ _)
    s (List.mem_filter.mp hs).1 hc

end CentralConfigurations
