import CentralConfigurations.Asymptotics.OrderSemantics
import CentralConfigurations.Diagrams.TwoColumn

/-!
# Maximal strokes, isolated components, and the second trace rule

Theorem 2.5 Rule 1e and Theorem 3.3(b) of Chang (2023). The argument uses an
equal-leading-position fiber inside an isolated component and the proved mass
balance. All nonempty subsystem mass sums must be nonzero.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

theorem OneColorLimit.no_maximal_stroke_no_circles {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (hm : AdmissibleMasses mass) (s : Finset (Fin n))
    (hclosed : ∀ i ∈ s, ∀ j, j ∉ s → q.force i j = 0)
    (hclose : ∀ i ∈ s, ∀ j ∈ s, q.force i j ≠ 0 → q.position i = q.position j) :
    ∀ i ∈ s, q.position i = 0 := by
  classical
  intro i hi
  let c := s.filter (fun j => q.position j = q.position i)
  apply q.coincident_component_circles_zero hm c i (Finset.mem_filter.mpr ⟨hi, rfl⟩)
  · intro j hj k hkc
    have hj' := Finset.mem_filter.mp hj
    by_cases hks : k ∈ s
    · by_contra hf
      have hpk : q.position k = q.position i := (hclose j hj'.1 k hks hf).symm.trans hj'.2
      exact hkc (Finset.mem_filter.mpr ⟨hks, hpk⟩)
    · exact hclosed j hj'.1 k hks
  · intro j hj _
    exact (Finset.mem_filter.mp hj).2

/-- Rule 1e in leading coefficients: a stroke is maximal exactly when its
endpoints have unequal leading positions. OrderSemantics proves this meaning. -/
theorem OneColorLimit.component_maximal_iff_circle {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (hm : AdmissibleMasses mass) (s : Finset (Fin n))
    (hclosed : ∀ i ∈ s, ∀ j, j ∉ s → q.force i j = 0) :
    (∃ i ∈ s, ∃ j ∈ s, q.force i j ≠ 0 ∧ q.position i ≠ q.position j) ↔
      (∃ i ∈ s, q.position i ≠ 0) := by
  classical
  constructor
  · rintro ⟨i, hi, j, hj, _, hp⟩
    by_cases hz : q.position i = 0
    · exact ⟨j, hj, fun hjz => hp (hz.trans hjz.symm)⟩
    · exact ⟨i, hi, hz⟩
  · rintro ⟨i, hi, hpi⟩
    by_contra hn
    apply hpi
    apply q.no_maximal_stroke_no_circles hm s hclosed _ i hi
    intro k hk r hr hf
    by_contra hp
    exact hn ⟨k, hk, r, hr, hf, hp⟩

theorem ScaledZWLimit.no_single_edges_z_positions_zero {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass)
    (hno : ∀ i j, i ≠ j → l.z.matrix i j + l.w.matrix i j ≠ 1) :
    ∀ i, l.z.position i = 0 := by
  classical
  intro i
  apply l.z.no_maximal_stroke_no_circles hm Finset.univ _ _ i (Finset.mem_univ i)
  · intro j _ k hk
    exact (hk (Finset.mem_univ k)).elim
  · intro j _ k _ hzf
    by_cases hjk : j = k
    · subst k
      rfl
    · have hwf : l.w.force j k ≠ 0 := by
        intro hw
        apply hno j k hjk
        simp [OneColorLimit.matrix, OneColorLimit.Incident, hjk, hzf, hw]
      exact l.w_stroke_z_close ha j k hjk hwf

/-- Theorem 3.3(b): absence of single-colored edges forces zero combined trace. -/
theorem ScaledZWLimit.no_single_edges_trace_zero {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass)
    (hno : ∀ i j, i ≠ j → l.z.matrix i j + l.w.matrix i j ≠ 1) :
    (∑ i, (l.z.matrix i i + l.w.matrix i i)) = 0 := by
  have hz := l.no_single_edges_z_positions_zero ha hm hno
  have hw : ∀ i, l.w.position i = 0 := l.swap.no_single_edges_z_positions_zero ha hm
    (fun i j hij => by
      change l.w.matrix i j + l.z.matrix i j ≠ 1
      rw [add_comm]
      exact hno i j hij)
  classical
  simp [OneColorLimit.matrix, OneColorLimit.Incident, hz, hw]

end CentralConfigurations
