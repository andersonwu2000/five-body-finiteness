import CentralConfigurations.Diagrams.MatrixRules

/-!
# Rule 2a and Theorem 3.1(b)

A stroke whose endpoints have equal leading positions cannot be isolated as
a two-vertex component unless their masses sum to zero. Apply this to each
color of a double edge, using the proved circling method.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

theorem OneColorLimit.close_stroke_has_external {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (i j : Fin n) (_hij : i ≠ j)
    (hm : mass i + mass j ≠ 0) (hp : q.position i = q.position j)
    (hf : q.force i j ≠ 0) :
    ∃ k, k ≠ i ∧ k ≠ j ∧ (q.force i k ≠ 0 ∨ q.force j k ≠ 0) := by
  classical
  by_contra hn
  have hz (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
      q.force i k = 0 ∧ q.force j k = 0 := by
    constructor
    · by_contra h
      exact hn ⟨k, hki, hkj, Or.inl h⟩
    · by_contra h
      exact hn ⟨k, hki, hkj, Or.inr h⟩
  have hi : q.position i = mass j * q.force i j := by
    rw [q.balance i, Finset.sum_eq_single j]
    · intro k _ hkj
      by_cases hki : k = i
      · subst k
        rw [q.diagonal, mul_zero]
      · rw [(hz k hki hkj).1, mul_zero]
    · simp
  have hj : q.position j = mass i * q.force j i := by
    rw [q.balance j, Finset.sum_eq_single i]
    · intro k _ hki
      by_cases hkj : k = j
      · subst k
        rw [q.diagonal, mul_zero]
      · rw [(hz k hki hkj).2, mul_zero]
    · simp
  rw [hi, hj, q.antisymm j i] at hp
  have hzero : (mass i + mass j) * q.force i j = 0 := by linear_combination hp
  exact mul_ne_zero hm hf hzero

/-- Rule 2a, expressed as simultaneous external-stroke existence for both colors. -/
theorem ScaledZWLimit.double_edge_external {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j) (hz : l.z.force i j ≠ 0) (hw : l.w.force i j ≠ 0) :
    (∃ k, k ≠ i ∧ k ≠ j ∧ (l.z.force i k ≠ 0 ∨ l.z.force j k ≠ 0)) ∧
    (∃ k, k ≠ i ∧ k ≠ j ∧ (l.w.force i k ≠ 0 ∨ l.w.force j k ≠ 0)) := by
  have hmij : mass i + mass j ≠ 0 := by
    simpa [hij] using hm {i, j} (by simp)
  exact ⟨l.z.close_stroke_has_external i j hij hmij (l.w_stroke_z_close ha i j hij hw) hz,
    l.w.close_stroke_has_external i j hij hmij (l.z_stroke_w_close ha i j hij hz) hw⟩

noncomputable def OneColorLimit.outsidePairSum {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (i j : Fin n) : ℕ :=
  ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), (q.matrix k i + q.matrix k j)

theorem OneColorLimit.outsidePairSum_pos {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (i j : Fin n)
    (h : ∃ k, k ≠ i ∧ k ≠ j ∧ (q.force i k ≠ 0 ∨ q.force j k ≠ 0)) :
    0 < q.outsidePairSum i j := by
  classical
  obtain ⟨k, hki, hkj, hf⟩ := h
  have hp : 0 < q.matrix k i + q.matrix k j := by
    rcases hf with hi | hj
    · have hh : q.matrix k i = 1 := by
        rw [q.matrix_symm k i]
        simp [matrix, Incident, Ne.symm hki, hi]
      rw [hh]
      omega
    · have hh : q.matrix k j = 1 := by
        rw [q.matrix_symm k j]
        simp [matrix, Incident, Ne.symm hkj, hj]
      rw [hh]
      omega
  exact Finset.sum_pos' (fun _ _ => Nat.zero_le _)
    ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ k, hki, hkj⟩, hp⟩

/-- Theorem 3.1(b) in its numerical matrix form. -/
theorem ScaledZWLimit.two_column_sums {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j) (hdouble : l.z.matrix i j + l.w.matrix i j = 2) :
    l.z.outsidePairSum i j * l.w.outsidePairSum i j ≠ 0 := by
  classical
  have hz : l.z.force i j ≠ 0 := by
    intro hzero
    have hh : l.z.matrix i j = 0 := by simp [OneColorLimit.matrix, OneColorLimit.Incident, hij, hzero]
    have hb := l.w.matrix_binary i j
    omega
  have hw : l.w.force i j ≠ 0 := by
    intro hzero
    have hh : l.w.matrix i j = 0 := by simp [OneColorLimit.matrix, OneColorLimit.Incident, hij, hzero]
    have hb := l.z.matrix_binary i j
    omega
  obtain ⟨hez, hew⟩ := l.double_edge_external ha hm i j hij hz hw
  exact mul_ne_zero (ne_of_gt (l.z.outsidePairSum_pos i j hez))
    (ne_of_gt (l.w.outsidePairSum_pos i j hew))

end CentralConfigurations
