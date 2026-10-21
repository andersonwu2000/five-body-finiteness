import CentralConfigurations.Diagrams.SourceComponents
import Mathlib.Data.Finset.Max

/-!
# The component extraction procedure in Appendix I

The source uses the single power A^(n-1), adds the least remaining vertex,
and removes each group before the next iteration. The groups are not assumed
to be ordinary graph components. The invariant needed for the matrix rules
is that the remaining circles in each ordinary component are all present or
all absent. Every group with a circle retains all circles of that component.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

def appendixGroup {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (remaining : Finset (Fin n)) (i : Fin n) : Finset (Fin n) :=
  insert i (remaining.filter (fun j => 0 < (integerMatrix A ^ (n - 1)) i j))

theorem appendixGroup_nonempty {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (remaining : Finset (Fin n)) (i : Fin n) : (appendixGroup A remaining i).Nonempty :=
  ⟨i, Finset.mem_insert_self _ _⟩

theorem appendixGroup_subset_remaining {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (remaining : Finset (Fin n)) (i : Fin n) (hi : i ∈ remaining) :
    appendixGroup A remaining i ⊆ remaining :=
  Finset.insert_subset hi (Finset.filter_subset _ _)

theorem appendixGroup_subset_component {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (remaining : Finset (Fin n)) (i : Fin n) :
    appendixGroup A remaining i ⊆ ordinaryComponent A hs i := by
  intro j hj
  apply (mem_ordinaryComponent _ _ _ _).mpr
  rcases Finset.mem_insert.mp hj with hji | hj
  · subst j
    exact .rfl
  · exact integerMatrix_pow_reachable A hs (n - 1) i j
      (ne_of_gt (Finset.mem_filter.mp hj).2)

theorem circle_mem_appendixGroup {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (remaining : Finset (Fin n)) (i j : Fin n)
    (h : (offDiagonalGraph A hs).Reachable i j) (hj : A j j = 1)
    (hjr : j ∈ remaining) : j ∈ appendixGroup A remaining i := by
  apply Finset.mem_insert_of_mem
  exact Finset.mem_filter.mpr ⟨hjr, reachable_loop_power_pos A hs i j h hj (n - 1) le_rfl⟩

/-- Circle membership in the remaining set is constant on each ordinary component. -/
def RemainingCirclesSaturated {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (remaining : Finset (Fin n)) : Prop :=
  ∀ i j, (offDiagonalGraph A hs).Reachable i j → A i i = 1 → A j j = 1 →
    (i ∈ remaining ↔ j ∈ remaining)

theorem remainingCirclesSaturated_univ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) : RemainingCirclesSaturated A hs Finset.univ := by
  intro i j _ _ _
  simp

theorem RemainingCirclesSaturated.group_circle_mem {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℕ} {hs : ∀ i j, A i j = A j i}
    {remaining : Finset (Fin n)} (h : RemainingCirclesSaturated A hs remaining)
    (seed : Fin n) (hseed : seed ∈ remaining) (i j : Fin n)
    (hij : (offDiagonalGraph A hs).Reachable i j) (hi : A i i = 1) (hj : A j j = 1)
    (hig : i ∈ appendixGroup A remaining seed) : j ∈ appendixGroup A remaining seed := by
  have hir := appendixGroup_subset_remaining A remaining seed hseed hig
  have hjr := (h i j hij hi hj).mp hir
  have hsi := (mem_ordinaryComponent _ _ _ _).mp
    (appendixGroup_subset_component A hs remaining seed hig)
  exact circle_mem_appendixGroup A hs remaining seed j (hsi.trans hij) hj hjr

theorem RemainingCirclesSaturated.remove_group {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℕ} {hs : ∀ i j, A i j = A j i}
    {remaining : Finset (Fin n)} (h : RemainingCirclesSaturated A hs remaining)
    (seed : Fin n) (hseed : seed ∈ remaining) :
    RemainingCirclesSaturated A hs (remaining \ appendixGroup A remaining seed) := by
  intro i j hij hi hj
  have hg : i ∈ appendixGroup A remaining seed ↔ j ∈ appendixGroup A remaining seed :=
    ⟨h.group_circle_mem seed hseed i j hij hi hj,
      h.group_circle_mem seed hseed j i hij.symm hj hi⟩
  simp only [Finset.mem_sdiff]
  exact and_congr (h i j hij hi hj) (not_congr hg)

theorem ScaledZWLimit.appendix_group_conclusion {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass)
    (remaining : Finset (Fin n))
    (hsat : RemainingCirclesSaturated l.z.matrix l.z.matrix_symm remaining)
    (seed : Fin n) (hseed : seed ∈ remaining) :
    ComponentMatrixConclusion l.z.matrix l.w.matrix (appendixGroup l.z.matrix remaining seed) := by
  classical
  by_cases hcircle : ∃ i ∈ appendixGroup l.z.matrix remaining seed, l.z.matrix i i = 1
  · obtain ⟨i, hi, hic⟩ := hcircle
    apply l.component_conclusion_of_circle_cover ha hm _
      (ordinaryComponent l.z.matrix l.z.matrix_symm seed)
      (ordinaryComponent_isolated l.z.matrix l.z.matrix_symm seed)
    refine ⟨appendixGroup_subset_component _ _ _ _, ?_⟩
    intro j hj hjc
    have hjone : l.z.matrix j j = 1 := (l.z.matrix_binary j j).resolve_left hjc
    have hsi := (mem_ordinaryComponent l.z.matrix l.z.matrix_symm seed i).mp
      (appendixGroup_subset_component l.z.matrix l.z.matrix_symm remaining seed hi)
    have hsj := (mem_ordinaryComponent _ _ _ _).mp hj
    exact hsat.group_circle_mem seed hseed i j (hsi.symm.trans hsj) hic hjone hi
  · have hz : ∀ i ∈ appendixGroup l.z.matrix remaining seed, l.z.matrix i i = 0 := by
      intro i hi
      exact (l.z.matrix_binary i i).resolve_right (fun h => hcircle ⟨i, hi, h⟩)
    refine ⟨?_, ?_⟩
    · rw [Finset.sum_eq_zero hz]
      decide
    · intro hne hall
      obtain ⟨i, hi⟩ := hne
      have := hz i hi
      have := hall i hi
      omega

theorem appendixGroup_sdiff_card_lt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (remaining : Finset (Fin n)) (i : Fin n) (hi : i ∈ remaining) :
    (remaining \ appendixGroup A remaining i).card < remaining.card :=
  Finset.card_lt_card (Finset.sdiff_ssubset (appendixGroup_subset_remaining A remaining i hi)
    (appendixGroup_nonempty A remaining i))

/-- The appendix's while-loop, including its least-remaining-index convention.
Strict decrease of the number of remaining indices proves termination. -/
def appendixComponentGroups {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (remaining : Finset (Fin n)) : List (Finset (Fin n)) :=
  if h : remaining.Nonempty then
    let seed := remaining.min' h
    let group := appendixGroup A remaining seed
    group :: appendixComponentGroups A (remaining \ group)
  else []
termination_by remaining.card
decreasing_by
  exact appendixGroup_sdiff_card_lt A remaining (remaining.min' h) (Finset.min'_mem remaining h)

/-- The routine returns only groups with more than one vertex. -/
def appendixComponents {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) : List (Finset (Fin n)) :=
  (appendixComponentGroups A Finset.univ).filter (fun s => 1 < s.card)

theorem ScaledZWLimit.appendix_component_groups_valid {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass)
    (remaining : Finset (Fin n)) :
    RemainingCirclesSaturated l.z.matrix l.z.matrix_symm remaining →
    ∀ s ∈ appendixComponentGroups l.z.matrix remaining,
      ComponentMatrixConclusion l.z.matrix l.w.matrix s := by
  induction remaining using Finset.strongInductionOn with
  | _ remaining ih =>
      intro hsat s hs
      rw [appendixComponentGroups] at hs
      split_ifs at hs with h
      · dsimp only at hs
        rcases List.mem_cons.mp hs with heq | hmem
        · subst s
          exact l.appendix_group_conclusion ha hm remaining hsat _ (Finset.min'_mem remaining h)
        · apply ih _ (Finset.sdiff_ssubset
            (appendixGroup_subset_remaining _ _ _ (Finset.min'_mem remaining h))
            (appendixGroup_nonempty _ _ _))
          · exact hsat.remove_group _ (Finset.min'_mem remaining h)
          · exact hmem
      · simp at hs

def AppendixComponentMatrixRule {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∀ s ∈ appendixComponents A, ComponentMatrixConclusion A B s

/-- Both connected-component conclusions hold on every group output by the
actual appendix routine. No graph-component/isolation equivalence is assumed. -/
theorem ScaledZWLimit.appendix_component_matrix_rule {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass) :
    AppendixComponentMatrixRule l.z.matrix l.w.matrix := by
  intro s hs
  exact l.appendix_component_groups_valid ha hm Finset.univ
    (remainingCirclesSaturated_univ _ _) s (List.mem_filter.mp hs).1

end CentralConfigurations
