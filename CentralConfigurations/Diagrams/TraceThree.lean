import CentralConfigurations.Diagrams.DoubleTriangles
import CentralConfigurations.Diagrams.ComponentRules

/-!
# The trace-three matrix rule

Chang (2023), Theorem 3.3(e). Nonzero subsystem mass sums forbid all three
circled leading positions from coinciding. A stroke from their center to an
uncircled vertex is maximal, so maximal-triangle closure supplies the edge
required by the matrix rule.
-/

namespace CentralConfigurations

open scoped BigOperators

theorem three_diagonals_exhaust {n : ℕ} (A : Fin n → Fin n → ℕ)
    (i j k r : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hri : r ≠ i) (hrj : r ≠ j) (hrk : r ≠ k)
    (ht : (∑ a, A a a) = 3) (hi : A i i = 1) (hj : A j j = 1) (hk : A k k = 1) :
    A r r = 0 := by
  have hs : (∑ a ∈ ({i, j, k, r} : Finset (Fin n)), A a a) = 3 + A r r := by
    simp [hij, hik, hjk, Ne.symm hri, Ne.symm hrj, Ne.symm hrk, hi, hj, hk]
    omega
  have hle : (∑ a ∈ ({i, j, k, r} : Finset (Fin n)), A a a) ≤ ∑ a, A a a :=
    Finset.sum_le_univ_sum_of_nonneg (fun a => Nat.zero_le (A a a))
  rw [hs, ht] at hle
  omega

def TraceThreeRule {n : ℕ} (A : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j k r, i ≠ j → i ≠ k → j ≠ k → r ≠ i → r ≠ j → r ≠ k →
    (∑ a, A a a) = 3 → A i i = 1 → A j j = 1 → A k k = 1 →
    A i j = 1 → A i k = 1 → A i r = 1 → A j r + A k r ≠ 0

theorem ScaledZWLimit.trace_three_rule {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass) :
    TraceThreeRule l.z.matrix := by
  classical
  intro i j k r hij hik hjk hri hrj hrk ht hi hj hk he₁ he₂ he₃
  have hpi : l.z.position i ≠ 0 := by simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hi
  have hzero : ∀ a, a ≠ i → a ≠ j → a ≠ k → l.z.position a = 0 := by
    intro a hai haj hak
    have h := three_diagonals_exhaust l.z.matrix i j k a hij hik hjk hai haj hak ht hi hj hk
    simpa [OneColorLimit.matrix, OneColorLimit.Incident] using h
  have hmax : l.z.position i ≠ l.z.position j ∨ l.z.position i ≠ l.z.position k := by
    by_contra hn
    push Not at hn
    apply hpi
    apply l.z.coincident_component_circles_zero hm Finset.univ i (Finset.mem_univ i)
    · intro a _ b hb'
      exact (hb' (Finset.mem_univ b)).elim
    · intro a _ hpa
      by_cases hai : a = i
      · exact hai ▸ rfl
      by_cases haj : a = j
      · simpa only [haj] using hn.1.symm
      by_cases hak : a = k
      · simpa only [hak] using hn.2.symm
      exact (hpa (hzero a hai haj hak)).elim
  have hmr : l.z.position i ≠ l.z.position r := by
    rw [hzero r hri hrj hrk]
    exact hpi
  have her : l.z.force i r ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, Ne.symm hri] using he₃
  rcases hmax with hmax | hmax
  · have he : l.z.force j i ≠ 0 := by
      have hji : l.z.matrix j i = 1 := (l.z.matrix_symm j i).trans he₁
      simpa [OneColorLimit.matrix, OneColorLimit.Incident, Ne.symm hij] using hji
    have h := l.maximal_z_triangle hb j i r (Ne.symm hij) (Ne.symm hri) (Ne.symm hrj)
      he (Ne.symm hmax) her hmr
    have hjr : l.z.matrix j r = 1 := by
      simp [OneColorLimit.matrix, OneColorLimit.Incident, Ne.symm hrj, h.1]
    omega
  · have he : l.z.force k i ≠ 0 := by
      have hki : l.z.matrix k i = 1 := (l.z.matrix_symm k i).trans he₂
      simpa [OneColorLimit.matrix, OneColorLimit.Incident, Ne.symm hik] using hki
    have h := l.maximal_z_triangle hb k i r (Ne.symm hik) (Ne.symm hri) (Ne.symm hrk)
      he (Ne.symm hmax) her hmr
    have hkr : l.z.matrix k r = 1 := by
      simp [OneColorLimit.matrix, OneColorLimit.Incident, Ne.symm hrk, h.1]
    omega

end CentralConfigurations
