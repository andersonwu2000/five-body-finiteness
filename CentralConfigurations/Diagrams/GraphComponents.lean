import CentralConfigurations.Diagrams.SourceConnectivity

/-!
# The appendix connectivity test and the isolated-set component rules

Appendix I, printed p.108, tests `I + A + ... + A^(n-1)` for zero entries.
This is distinct from Definition 3.2 and from the component extraction routine
on pp.112--113. We prove the companion-trace conclusion for the actual test.
We also reconstruct Theorem 3.7(b) under the explicit isolation premise used
by its proof. SourceComponents and AppendixComponents supply the circle-cover
bridges to the other conventions; no equality of the component sets is assumed.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

/-- The literal `ConnectedMatrixQ` expression in Appendix I. -/
def algorithmConnectivityMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) :
    Matrix (Fin n) (Fin n) ℤ :=
  1 + ∑ k ∈ Finset.Icc 1 (n - 1), (Matrix.of (fun i j => (A i j : ℤ))) ^ k

def AlgorithmFullyConnected {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∀ i j, algorithmConnectivityMatrix A i j ≠ 0

theorem algorithmConnectivity_preserves_labels {n : ℕ} {α : Type*}
    (A : Matrix (Fin n) (Fin n) ℕ) (p : Fin n → α)
    (hA : ∀ i j, A i j ≠ 0 → p i = p j) (i j : Fin n)
    (h : algorithmConnectivityMatrix A i j ≠ 0) : p i = p j := by
  by_contra hp
  apply h
  have hij : i ≠ j := fun e => hp (congrArg p e)
  have hpow : ∀ k, ((Matrix.of (fun u v => (A u v : ℤ))) ^ k) i j = 0 := by
    intro k
    by_contra hk
    apply hp
    apply matrix_pow_preserves_labels (Matrix.of (fun u v => (A u v : ℤ))) p _ k i j hk
    intro u v huv
    apply hA u v
    intro hz
    simp [hz] at huv
  simp [algorithmConnectivityMatrix, Matrix.add_apply, Matrix.sum_apply,
    hij, hpow]

def AlgorithmFullyConnectedCompanionRule {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  AlgorithmFullyConnected A → (∑ i, B i i) = 0

/-- The fully-connected companion filter with the appendix's actual test. -/
theorem ScaledZWLimit.algorithm_fully_connected_companion_trace {n : ℕ}
    {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ}
    (l : ScaledZWLimit q a) (ha : Tendsto a atTop (𝓝 0))
    (hm : AdmissibleMasses mass) :
    AlgorithmFullyConnectedCompanionRule l.z.matrix l.w.matrix := by
  intro hc
  have hclose : ∀ i j, l.w.position i = l.w.position j := by
    intro i j
    apply algorithmConnectivity_preserves_labels l.z.matrix l.w.position _ i j (hc i j)
    intro u v huv
    by_cases heq : u = v
    · exact congrArg l.w.position heq
    · apply l.z_stroke_w_close ha u v heq
      intro hf
      simp [OneColorLimit.matrix, OneColorLimit.Incident, heq, hf] at huv
  have hz : ∀ i, l.w.position i = 0 := by
    intro i
    apply l.w.coincident_component_circles_zero hm Finset.univ i (Finset.mem_univ i)
    · intro j _ k hk
      exact (hk (Finset.mem_univ k)).elim
    · intro j _ _
      exact hclose j i
  classical
  simp [OneColorLimit.matrix, OneColorLimit.Incident, hz]

/-- A finite vertex set with no edge to its complement. -/
def MatrixIsolated {n : ℕ} (A : Fin n → Fin n → ℕ) (s : Finset (Fin n)) : Prop :=
  ∀ i ∈ s, ∀ j, j ∉ s → A i j = 0

theorem OneColorLimit.matrix_isolated_force {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) {s : Finset (Fin n)} (hs : MatrixIsolated q.matrix s) :
    ∀ i ∈ s, ∀ j, j ∉ s → q.force i j = 0 := by
  intro i hi j hj
  have hij : i ≠ j := fun e => hj (e ▸ hi)
  have h := hs i hi j hj
  simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij] using h

/-- Theorem 3.7(b)(i) for an explicitly isolated set. -/
theorem OneColorLimit.isolated_trace_ne_one {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (hm : ∀ i, mass i ≠ 0)
    (s : Finset (Fin n)) (hs : MatrixIsolated q.matrix s) :
    (∑ i ∈ s, q.matrix i i) ≠ 1 := by
  classical
  intro ht
  have hc : (s.filter (fun i => q.position i ≠ 0)).card = 1 := by
    simpa only [matrix, Incident, if_pos rfl, Finset.sum_boole] using ht
  obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
  have hic : i ∈ s.filter (fun j => q.position j ≠ 0) := by rw [hi]; simp
  have his := (Finset.mem_filter.mp hic).1
  apply (Finset.mem_filter.mp hic).2
  apply q.no_unique_component_circle s i his (hm i) (q.matrix_isolated_force hs)
  intro j hjs hji
  by_contra hj
  have hjc : j ∈ s.filter (fun k => q.position k ≠ 0) := Finset.mem_filter.mpr ⟨hjs, hj⟩
  rw [hi] at hjc
  exact hji (Finset.mem_singleton.mp hjc)

/-- Theorem 3.7(b)(ii), retaining the nonempty isolated-set premise explicitly. -/
theorem ScaledZWLimit.isolated_not_fully_double {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : MatrixIsolated l.z.matrix s) (hne : s.Nonempty)
    (hc : ∀ i ∈ s, l.z.matrix i i = 1) :
    ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ l.z.matrix i j + l.w.matrix i j ≠ 2 := by
  classical
  by_contra hn
  obtain ⟨i, hi⟩ := hne
  have hip : l.z.position i ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hc i hi
  apply hip
  apply l.z.coincident_component_circles_zero hm s i hi (l.z.matrix_isolated_force hs)
  intro j hj _
  by_cases hji : j = i
  · exact congrArg l.z.position hji
  have hdouble : l.z.matrix j i + l.w.matrix j i = 2 := by
    by_contra h
    exact hn ⟨j, hj, i, hi, hji, h⟩
  have hw : l.w.matrix j i = 1 := by
    have hz := l.z.matrix_binary j i
    have hw := l.w.matrix_binary j i
    omega
  apply l.w_stroke_z_close ha j i hji
  simpa [OneColorLimit.matrix, OneColorLimit.Incident, hji] using hw

def IsolatedComponentMatrixRule {n : ℕ} (A B : Fin n → Fin n → ℕ) : Prop :=
  ∀ s : Finset (Fin n), MatrixIsolated A s →
    (∑ i ∈ s, A i i) ≠ 1 ∧
    (s.Nonempty → (∀ i ∈ s, A i i = 1) →
      ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ A i j + B i j ≠ 2)

theorem ScaledZWLimit.isolated_component_matrix_rule {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass) :
    IsolatedComponentMatrixRule l.z.matrix l.w.matrix := by
  intro s hs
  have hmi : ∀ i, mass i ≠ 0 := by
    intro i
    simpa using hm {i} (by simp)
  exact ⟨l.z.isolated_trace_ne_one hmi s hs, l.isolated_not_fully_double ha hm s hs⟩

end CentralConfigurations
