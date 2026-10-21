import CentralConfigurations.Asymptotics.Balancing
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Binary matrices from actual leading coefficients

Definition 3.1 and the first necessary filters in Chang (2023). The matrix is
defined solely from nonzero limiting coefficients. Its rules are consequences
of the force equations and two-color limit theorems, not fields in its definition.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

namespace OneColorLimit

variable {n : ℕ} {mass : Fin n → ℂ}

def Incident (q : OneColorLimit ℂ n mass) (i j : Fin n) : Prop :=
  if i = j then q.position i ≠ 0 else q.force i j ≠ 0

noncomputable def matrix (q : OneColorLimit ℂ n mass) (i j : Fin n) : ℕ := by
  classical
  exact if q.Incident i j then 1 else 0

noncomputable def incidentSet (q : OneColorLimit ℂ n mass) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (q.Incident i)

theorem matrix_binary (q : OneColorLimit ℂ n mass) (i j : Fin n) :
    q.matrix i j = 0 ∨ q.matrix i j = 1 := by
  classical
  by_cases h : q.Incident i j <;> simp [matrix, h]

theorem incident_symm (q : OneColorLimit ℂ n mass) (i j : Fin n) :
    q.Incident i j ↔ q.Incident j i := by
  by_cases h : i = j
  · subst j
    rfl
  · simp only [Incident, if_neg h, if_neg (Ne.symm h)]
    rw [q.antisymm i j, neg_ne_zero]

theorem matrix_symm (q : OneColorLimit ℂ n mass) (i j : Fin n) :
    q.matrix i j = q.matrix j i := by
  classical
  simp only [matrix, q.incident_symm i j]

theorem incident_not_unique (q : OneColorLimit ℂ n mass) (hm : ∀ i, mass i ≠ 0)
    (i j : Fin n) (h : q.Incident i j) : ∃ k, k ≠ j ∧ q.Incident i k := by
  classical
  by_cases hij : i = j
  · subst j
    have hp : q.position i ≠ 0 := by simpa [Incident] using h
    obtain ⟨k, hki, hk⟩ := q.circle_has_stroke i hp
    exact ⟨k, hki, by simpa [Incident, hki.symm] using hk⟩
  · have hf : q.force i j ≠ 0 := by simpa [Incident, hij] using h
    by_cases hp : q.position i = 0
    · by_contra hn
      have hother : ∀ k, k ≠ j → q.force i k = 0 := by
        intro k hkj
        by_cases hki : k = i
        · subst k
          exact q.diagonal i
        · by_contra hk
          exact hn ⟨k, hkj, by simpa [Incident, Ne.symm hki] using hk⟩
      exact q.single_stroke_circled i j (hm j) hf hother hp
    · exact ⟨i, hij, by simpa [Incident] using hp⟩

theorem incidentSet_card_ne_one (q : OneColorLimit ℂ n mass) (hm : ∀ i, mass i ≠ 0)
    (i : Fin n) : (q.incidentSet i).card ≠ 1 := by
  classical
  intro hc
  obtain ⟨j, hj⟩ := Finset.card_eq_one.mp hc
  have hmem : j ∈ q.incidentSet i := by rw [hj]; simp
  have hi : q.Incident i j := (Finset.mem_filter.mp hmem).2
  obtain ⟨k, hkj, hk⟩ := q.incident_not_unique hm i j hi
  have hkset : k ∈ q.incidentSet i := Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩
  rw [hj] at hkset
  exact hkj (Finset.mem_singleton.mp hkset)

theorem row_sum_eq_card (q : OneColorLimit ℂ n mass) (i : Fin n) :
    (∑ j, q.matrix i j) = (q.incidentSet i).card := by
  classical
  simp [matrix, incidentSet]

/-- Theorem 3.1(a), the exclusion of a column sum of one. -/
theorem column_sum_ne_one (q : OneColorLimit ℂ n mass) (hm : ∀ i, mass i ≠ 0)
    (j : Fin n) : (∑ i, q.matrix i j) ≠ 1 := by
  simp_rw [q.matrix_symm _ j]
  rw [q.row_sum_eq_card]
  exact q.incidentSet_card_ne_one hm j

theorem Nonzero.exists_stroke {q : OneColorLimit ℂ n mass} (h : q.Nonzero) :
    ∃ i j, i ≠ j ∧ q.force i j ≠ 0 := by
  rcases h with ⟨i, hi⟩ | ⟨i, j, hij⟩
  · obtain ⟨j, hji, hf⟩ := q.circle_has_stroke i hi
    exact ⟨i, j, hji.symm, hf⟩
  · refine ⟨i, j, ?_, hij⟩
    intro heq
    subst j
    exact hij (q.diagonal i)

/-- The other assertion in Theorem 3.1(a): a nonzero color has a nonzero column. -/
theorem Nonzero.exists_nonzero_column {q : OneColorLimit ℂ n mass} (h : q.Nonzero) :
    ∃ j, (∑ i, q.matrix i j) ≠ 0 := by
  classical
  obtain ⟨i, j, hij, hf⟩ := h.exists_stroke
  have hm : q.matrix i j = 1 := by simp [matrix, Incident, hij, hf]
  refine ⟨j, ?_⟩
  intro hs
  have hh := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => Nat.zero_le (q.matrix k j))
    (Finset.mem_univ i)
  rw [hm, hs] at hh
  exact Nat.not_succ_le_zero 0 hh

/-- Theorem 3.3(a): the diagonal cannot have exactly one circle. -/
theorem trace_ne_one (q : OneColorLimit ℂ n mass) (hm : ∀ i, mass i ≠ 0) :
    (∑ i, q.matrix i i) ≠ 1 := by
  classical
  intro hs
  have hc : (Finset.univ.filter (fun i => q.position i ≠ 0)).card = 1 := by
    simpa only [matrix, Incident, if_pos rfl, Finset.sum_boole] using hs
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  have hip : q.position i ≠ 0 := by
    have hmem : i ∈ Finset.univ.filter (fun k => q.position k ≠ 0) := by rw [hi]; simp
    exact (Finset.mem_filter.mp hmem).2
  apply hip
  apply q.no_unique_component_circle Finset.univ i (Finset.mem_univ i) (hm i)
  · intro j _ k hk
    exact (hk (Finset.mem_univ k)).elim
  · intro j _ hji
    by_contra hj
    have hmem : j ∈ Finset.univ.filter (fun k => q.position k ≠ 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
    rw [hi] at hmem
    exact hji (Finset.mem_singleton.mp hmem)

end OneColorLimit

/-- Theorem 3.2, one of its two symmetric assertions. -/
theorem ScaledZWLimit.w_circling_matrix {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (i j : Fin n) (hij : i ≠ j) :
    l.w.matrix i j * (l.z.matrix i i + l.z.matrix j j) ≠ 1 := by
  classical
  by_cases hw : l.w.force i j = 0
  · simp [OneColorLimit.matrix, OneColorLimit.Incident, hij, hw]
  · have hp := l.w_stroke_z_close ha i j hij hw
    by_cases hz : l.z.position i = 0
    · have hj : l.z.position j = 0 := hp.symm.trans hz
      simp [OneColorLimit.matrix, OneColorLimit.Incident, hij, hw, hz, hj]
    · have hj : l.z.position j ≠ 0 := by rw [← hp]; exact hz
      simp [OneColorLimit.matrix, OneColorLimit.Incident, hij, hw, hz, hj]

theorem ScaledZWLimit.z_circling_matrix {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (i j : Fin n) (hij : i ≠ j) :
    l.z.matrix i j * (l.w.matrix i i + l.w.matrix j j) ≠ 1 :=
  l.swap.w_circling_matrix ha i j hij

end CentralConfigurations
