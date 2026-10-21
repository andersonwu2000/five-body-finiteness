import CentralConfigurations.Diagrams.DoubleTriangles
import CentralConfigurations.Diagrams.ComponentRules

/-!
# The first trace-two matrix rule

Chang (2023), Theorem 3.3(c). When exactly two leading positions are nonzero,
weighted balance makes them distinct. Each is therefore separated at maximal
order from every other vertex. The opposite force equations put both opposite
positions at order O(epsilon^2); Estimate 1 forces the joining maximal stroke.
This reconstructs the rule directly from the equations and proved estimates,
without assuming Proposition 2.7 or choosing square-root branches.
-/

namespace CentralConfigurations

open Filter Asymptotics
open scoped BigOperators

/-- A maximal separation makes the opposite force O(epsilon^2). -/
theorem PairEstimateData.wForce_small_of_z_maximal (p : PairEstimateData)
    (hz : p.z =Θ[atTop] p.scale) :
    p.wForce =O[atTop] (fun t => p.eps t ^ 2) := by
  have h : (fun t => p.wForce t ^ 2) =O[atTop] (fun t => (p.eps t ^ 2) ^ 2) :=
    ((hz.inv.1.pow 3).mul p.swap.inv_z_upper).congr
      (fun t => by
        change (p.z t)⁻¹ ^ 3 * (p.w t)⁻¹ = p.wForce t ^ 2
        rw [p.inv_z_cube t, mul_assoc, mul_inv_cancel₀ (p.w_ne_zero t), mul_one])
      (fun t => by
        dsimp [PairEstimateData.scale, PairEstimateData.swap]
        field_simp [p.eps_ne_zero t])
  exact IsBigO.of_pow (by decide : (2 : ℕ) ≠ 0) h

theorem two_diagonals_exhaust {n : ℕ} (A : Fin n → Fin n → ℕ)
    (i j k : Fin n) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (ht : (∑ a, A a a) = 2) (hi : A i i = 1) (hj : A j j = 1) : A k k = 0 := by
  have hs : (∑ a ∈ ({i, j, k} : Finset (Fin n)), A a a) = 2 + A k k := by
    simp [hij, Ne.symm hki, Ne.symm hkj, hi, hj]
    omega
  have hle : (∑ a ∈ ({i, j, k} : Finset (Fin n)), A a a) ≤ ∑ a, A a a :=
    Finset.sum_le_univ_sum_of_nonneg (fun a => Nat.zero_le (A a a))
  rw [hs, ht] at hle
  omega

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

/-- An isolated leading z-position has an opposite position O(epsilon^2).
Here "isolated" means unequal to every other leading position, not an isolated
vertex in the stroke graph. -/
theorem w_position_small_of_unique_z_position (i : Fin n)
    (hp : ∀ j, j ≠ i → l.z.position i ≠ l.z.position j) :
    (fun t => (q t).w i) =O[atTop] (fun t => ((q t).epsilon : ℂ) ^ 2) := by
  have hf (j : Fin n) : (fun t => (q t).wForce i j) =O[atTop]
      (fun t => ((q t).epsilon : ℂ) ^ 2) := by
    by_cases hji : j = i
    · subst j
      simpa [ZWSystem.wForce] using
        (isBigO_zero (fun t => ((q t).epsilon : ℂ) ^ 2) atTop)
    · exact (ZWSystem.pairEstimateData q hb i j (Ne.symm hji)).wForce_small_of_z_maximal
        ((l.pair_z_maximal_iff hb i j (Ne.symm hji)).mpr (hp j hji))
  have hs := IsBigO.sum (s := Finset.univ) (fun j _ => (hf j).const_mul_left (mass j))
  exact hs.congr_left (fun t => by
    rw [(q t).force_w i]
    apply Finset.sum_congr rfl
    intro j _
    simp only [ZWSystem.wForce]
    ring)

omit hb in
/-- Exactly two circles give distinct nonzero leading positions. -/
theorem trace_two_positions {i j : Fin n} (hm : AdmissibleMasses mass)
    (hij : i ≠ j) (ht : (∑ a, l.z.matrix a a) = 2)
    (hi : l.z.matrix i i = 1) (hj : l.z.matrix j j = 1) :
    l.z.position i ≠ l.z.position j ∧
      (∀ k, k ≠ i → l.z.position i ≠ l.z.position k) ∧
      (∀ k, k ≠ j → l.z.position j ≠ l.z.position k) := by
  classical
  have hpi : l.z.position i ≠ 0 := by simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hi
  have hpj : l.z.position j ≠ 0 := by simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hj
  have hzero : ∀ k, k ≠ i → k ≠ j → l.z.position k = 0 := by
    intro k hki hkj
    have hk := two_diagonals_exhaust l.z.matrix i j k hij hki hkj ht hi hj
    simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hk
  have hneq : l.z.position i ≠ l.z.position j := by
    intro heq
    apply hpi
    apply l.z.coincident_component_circles_zero hm Finset.univ i (Finset.mem_univ i)
    · intro k _ r hr
      exact (hr (Finset.mem_univ r)).elim
    · intro k _ hk
      by_cases hki : k = i
      · exact hki ▸ rfl
      by_cases hkj : k = j
      · exact hkj ▸ heq.symm
      exact (hk (hzero k hki hkj)).elim
  refine ⟨hneq, ?_, ?_⟩
  · intro k hki
    by_cases hkj : k = j
    · exact hkj ▸ hneq
    · rw [hzero k hki hkj]
      exact hpi
  · intro k hkj
    by_cases hki : k = i
    · exact hki ▸ hneq.symm
    · rw [hzero k hki hkj]
      exact hpj

theorem trace_two_joining_stroke {i j : Fin n} (hm : AdmissibleMasses mass)
    (hij : i ≠ j) (ht : (∑ a, l.z.matrix a a) = 2)
    (hi : l.z.matrix i i = 1) (hj : l.z.matrix j j = 1) :
    l.z.force i j ≠ 0 ∧ l.z.position i ≠ l.z.position j := by
  have hp := l.trace_two_positions hm hij ht hi hj
  have hwi := l.w_position_small_of_unique_z_position hb i hp.2.1
  have hwj := l.w_position_small_of_unique_z_position hb j hp.2.2
  let p := ZWSystem.pairEstimateData q hb i j hij
  have hw : p.w =Θ[atTop] (fun t => p.eps t ^ 2) := ⟨hwi.sub hwj, p.w_lower⟩
  have hz := p.maximal_iff_w_small.mpr hw
  exact ⟨(l.pair_z_stroke_iff hb i j hij).mp hz.1, hp.1⟩

end ScaledZWLimit

def TraceTwoRule {n : ℕ} (A : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j, i ≠ j → (∑ a, A a a) = 2 → A i i = 1 → A j j = 1 →
    A i j = 1 ∧ ∀ k, k ≠ i → k ≠ j → A i k = A j k

/-- Theorem 3.3(c), in the matrix representation. -/
theorem ScaledZWLimit.trace_two_rule {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass) :
    TraceTwoRule l.z.matrix := by
  classical
  intro i j hij ht hi hj
  have he := l.trace_two_joining_stroke hb hm hij ht hi hj
  have hp := l.trace_two_positions hm hij ht hi hj
  have hmij : l.z.matrix i j = 1 := by
    simp [OneColorLimit.matrix, OneColorLimit.Incident, hij, he.1]
  refine ⟨hmij, ?_⟩
  intro k hki hkj
  have hleft : l.z.matrix i k = 1 → l.z.matrix j k = 1 := by
    intro hik
    have hfi : l.z.force i k ≠ 0 := by
      simpa [OneColorLimit.matrix, OneColorLimit.Incident, hki.symm] using hik
    have hfji : l.z.force j i ≠ 0 := by rw [l.z.antisymm j i]; exact neg_ne_zero.mpr he.1
    have h := l.maximal_z_triangle hb j i k hij.symm hki.symm hkj.symm
      hfji he.2.symm hfi (hp.2.1 k hki)
    simp [OneColorLimit.matrix, OneColorLimit.Incident, hkj.symm, h.1]
  have hright : l.z.matrix j k = 1 → l.z.matrix i k = 1 := by
    intro hjk
    have hfj : l.z.force j k ≠ 0 := by
      simpa [OneColorLimit.matrix, OneColorLimit.Incident, hkj.symm] using hjk
    have h := l.maximal_z_triangle hb i j k hij hkj.symm hki.symm
      he.1 he.2 hfj (hp.2.2 k hkj)
    simp [OneColorLimit.matrix, OneColorLimit.Incident, hki.symm, h.1]
  rcases l.z.matrix_binary i k with hik | hik
  · rcases l.z.matrix_binary j k with hjk | hjk
    · exact hik.trans hjk.symm
    · have := hright hjk
      omega
  · exact hik.trans (hleft hik).symm

/-- The row-vanishing conclusion in the first sentence of Theorem 3.3(d).
The cubic-mass/trace exclusion is proved separately in TraceTwoCubic. -/
theorem ScaledZWLimit.trace_two_companion_rows_zero {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (nhds 0))
    (hm : AdmissibleMasses mass) (i j : Fin n) (hij : i ≠ j)
    (ht : (∑ a, l.z.matrix a a) = 2) (hi : l.z.matrix i i = 1)
    (hj : l.z.matrix j j = 1) : ∀ k, l.w.matrix i k = 0 ∧ l.w.matrix j k = 0 := by
  classical
  have hp := l.trace_two_positions hm hij ht hi hj
  have hrow (r : Fin n) (hr : ∀ k, k ≠ r → l.z.position r ≠ l.z.position k) :
      ∀ k, l.w.matrix r k = 0 := by
    have hf : ∀ k, l.w.force r k = 0 := by
      intro k
      by_cases hkr : k = r
      · subst k
        exact l.w.diagonal r
      · by_contra hfk
        exact hr k hkr (l.w_stroke_z_close ha r k (Ne.symm hkr) hfk)
    have hz : l.w.position r = 0 := by rw [l.w.balance r]; simp [hf]
    intro k
    simp [OneColorLimit.matrix, OneColorLimit.Incident, hf, hz]
  exact fun k => ⟨hrow i hp.2.1 k, hrow j hp.2.2 k⟩

def TraceTwoCompanionRowsRule {n : ℕ} (A B : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j, i ≠ j → (∑ a, A a a) = 2 → A i i = 1 → A j j = 1 →
    ∀ k, B i k = 0 ∧ B j k = 0

end CentralConfigurations
