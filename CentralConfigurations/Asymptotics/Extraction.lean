import CentralConfigurations.Asymptotics.OneColor
import Mathlib.Topology.Sequences
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.Basic

/-!
# Compact extraction of a nonzero normalized leading vector

This is the finite-dimensional compactness step in Section 2.2 of Chang (2023).
Both individual and simultaneous z/w extraction are provided. The balanced
rescaling and unboundedness identifying a singular sequence are handled separately.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

noncomputable def unitNormalize {ι : Type*} [Fintype ι] (v : ι → ℂ) : ι → ℂ :=
  ((‖v‖ : ℂ)⁻¹) • v

theorem norm_unitNormalize {ι : Type*} [Fintype ι] (v : ι → ℂ) (hv : v ≠ 0) :
    ‖unitNormalize v‖ = 1 := by
  simp only [unitNormalize, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg v)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)

theorem exists_normalized_subsequence {ι : Type*} [Fintype ι]
    (v : ℕ → ι → ℂ) (hv : ∀ t, v t ≠ 0) :
    ∃ l : ι → ℂ, ‖l‖ = 1 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun t => unitNormalize (v (φ t))) atTop (𝓝 l) := by
  obtain ⟨l, hl, φ, hφ, hlim⟩ :=
    (isCompact_sphere (0 : ι → ℂ) 1).tendsto_subseq
      (fun t => show unitNormalize (v t) ∈ Metric.sphere 0 1 by
        simpa [Metric.mem_sphere, dist_zero_right] using norm_unitNormalize (v t) (hv t))
  exact ⟨l, by simpa [Metric.mem_sphere, dist_zero_right] using hl, φ, hφ, hlim⟩

/-- One subsequence works for both normalized vectors, and both limits have norm one. -/
theorem exists_simultaneous_normalized_subsequence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : ℕ → ι → ℂ) (w : ℕ → κ → ℂ) (hv : ∀ t, v t ≠ 0) (hw : ∀ t, w t ≠ 0) :
    ∃ l : ι → ℂ, ∃ r : κ → ℂ, ‖l‖ = 1 ∧ ‖r‖ = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun t => unitNormalize (v (φ t))) atTop (𝓝 l) ∧
        Tendsto (fun t => unitNormalize (w (φ t))) atTop (𝓝 r) := by
  let s := Metric.sphere (0 : ι → ℂ) 1
  let u := Metric.sphere (0 : κ → ℂ) 1
  have hc : IsCompact (s ×ˢ u) := (isCompact_sphere _ _).prod (isCompact_sphere _ _)
  obtain ⟨⟨l, r⟩, hlr, φ, hφ, hlim⟩ := hc.tendsto_subseq
    (fun t => show (unitNormalize (v t), unitNormalize (w t)) ∈ s ×ˢ u from
      ⟨by simpa [s, Metric.mem_sphere, dist_zero_right] using norm_unitNormalize (v t) (hv t),
       by simpa [u, Metric.mem_sphere, dist_zero_right] using norm_unitNormalize (w t) (hw t)⟩)
  refine ⟨l, r, ?_, ?_, φ, hφ, ?_, ?_⟩
  · simpa [s, Metric.mem_sphere, dist_zero_right] using hlr.1
  · simpa [u, Metric.mem_sphere, dist_zero_right] using hlr.2
  · exact (continuous_fst.tendsto (l, r)).comp hlim
  · exact (continuous_snd.tendsto (l, r)).comp hlim

abbrev ColorCoordinate (n : ℕ) := Fin n ⊕ (Fin n × Fin n)

def ZWSystem.zVector {n : ℕ} {mass : Fin n → ℂ} (q : ZWSystem ℂ n mass) :
    ColorCoordinate n → ℂ
  | .inl i => q.z i
  | .inr (i, j) => q.delta i j ^ 3 * (q.z i - q.z j)

def ZWSystem.wVector {n : ℕ} {mass : Fin n → ℂ} (q : ZWSystem ℂ n mass) :
    ColorCoordinate n → ℂ := q.swap.zVector

theorem ZWSystem.zVector_rescale {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (a : ℂ) (ha : a ≠ 0) :
    (q.rescale a ha).zVector = a • q.zVector := by
  funext c
  rcases c with i | ⟨i, j⟩
  · rfl
  · simp only [zVector, rescale, Pi.smul_apply, smul_eq_mul]
    ring

theorem ZWSystem.wVector_rescale {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (a : ℂ) (ha : a ≠ 0) :
    (q.rescale a ha).wVector = a⁻¹ • q.wVector := by
  funext c
  rcases c with i | ⟨i, j⟩
  · rfl
  · simp only [wVector, zVector, swap, rescale, Pi.smul_apply, smul_eq_mul]
    ring

theorem ZWSystem.zVector_ne_zero {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) : q.zVector ≠ 0 := by
  intro h
  have hi := congrFun h (.inl i)
  have hj := congrFun h (.inl j)
  apply q.z_separation_ne_zero hij
  simpa [ZWSystem.zVector] using congrArg₂ (· - ·) hi hj

/-- The extracted coefficients satisfy all the balance equations and are not
all zero. This does not assert that the original sequence is singular. -/
theorem exists_nonzero_z_limit {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) :
    ∃ l : OneColorLimit ℂ n mass,
      (∃ k, l.position k ≠ 0) ∨ (∃ k r, l.force k r ≠ 0) := by
  obtain ⟨v, hv, φ, _, hlim⟩ := exists_normalized_subsequence
    (fun t => (q t).zVector) (fun t => (q t).zVector_ne_zero i j hij)
  let seq := fun t => (q (φ t)).scaledZ ((‖(q (φ t)).zVector‖ : ℂ)⁻¹)
  have hp : ∀ k, Tendsto (fun t => (seq t).position k) atTop (𝓝 (v (.inl k))) := by
    intro k
    exact ((continuous_apply (Sum.inl k : ColorCoordinate n)).tendsto v).comp hlim
  have hf : ∀ k r, Tendsto (fun t => (seq t).force k r) atTop (𝓝 (v (.inr (k, r)))) := by
    intro k r
    have h := ((continuous_apply (Sum.inr (k, r) : ColorCoordinate n)).tendsto v).comp hlim
    simpa only [unitNormalize, Pi.smul_apply, smul_eq_mul, ZWSystem.zVector, seq,
      ZWSystem.scaledZ, mul_assoc] using h
  let l := OneColorLimit.ofLimit seq (fun k => v (.inl k)) (fun k r => v (.inr (k, r))) hp hf
  refine ⟨l, ?_⟩
  classical
  by_contra hn
  have hz : v = 0 := by
    funext c
    rcases c with k | ⟨k, r⟩
    · by_contra h
      exact hn (Or.inl ⟨k, h⟩)
    · by_contra h
      exact hn (Or.inr ⟨k, r, h⟩)
  rw [hz, norm_zero] at hv
  exact zero_ne_one hv

end CentralConfigurations
