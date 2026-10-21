import CentralConfigurations.Asymptotics.TwoColor
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The balanced normalization of Section 2.3

Positive reciprocal rescaling equalizes the two vector norms. Their product
is invariant, so the common norm is its square root. In particular, a sequence
with norm product tending to infinity acquires a common inverse scale tending
to zero. No rotational-gauge preservation is claimed.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

noncomputable def ZWSystem.balanceFactor {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) : ℝ := Real.sqrt (‖q.wVector‖ / ‖q.zVector‖)

theorem ZWSystem.balanceFactor_pos {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) : 0 < q.balanceFactor := by
  apply Real.sqrt_pos.mpr
  exact div_pos (norm_pos_iff.mpr (q.swap.zVector_ne_zero i j hij))
    (norm_pos_iff.mpr (q.zVector_ne_zero i j hij))

noncomputable def ZWSystem.balanced {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) : ZWSystem ℂ n mass :=
  q.rescale q.balanceFactor (Complex.ofReal_ne_zero.mpr (ne_of_gt (q.balanceFactor_pos i j hij)))

theorem ZWSystem.balanced_norms {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) :
    ‖(q.balanced i j hij).zVector‖ = ‖(q.balanced i j hij).wVector‖ := by
  have hp := q.balanceFactor_pos i j hij
  have hz : ‖q.zVector‖ ≠ 0 := norm_ne_zero_iff.mpr (q.zVector_ne_zero i j hij)
  have hsq : q.balanceFactor ^ 2 * ‖q.zVector‖ = ‖q.wVector‖ := by
    rw [balanceFactor, Real.sq_sqrt (div_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact div_mul_cancel₀ _ hz
  unfold balanced
  rw [q.zVector_rescale, q.wVector_rescale, norm_smul, norm_smul, norm_inv]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp]
  apply (mul_left_cancel₀ (ne_of_gt hp))
  simp only [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hp), one_mul]
  nlinarith [hsq]

theorem ZWSystem.norm_product_rescale {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (a : ℂ) (ha : a ≠ 0) :
    ‖(q.rescale a ha).zVector‖ * ‖(q.rescale a ha).wVector‖ =
      ‖q.zVector‖ * ‖q.wVector‖ := by
  rw [q.zVector_rescale, q.wVector_rescale, norm_smul, norm_smul, norm_inv]
  calc
    _ = (‖a‖ * ‖a‖⁻¹) * (‖q.zVector‖ * ‖q.wVector‖) := by ring
    _ = _ := by rw [mul_inv_cancel₀ (norm_ne_zero_iff.mpr ha), one_mul]

theorem ZWSystem.norm_balanced_eq_sqrt {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) :
    ‖(q.balanced i j hij).zVector‖ = Real.sqrt (‖q.zVector‖ * ‖q.wVector‖) := by
  have hprod := q.norm_product_rescale q.balanceFactor
    (Complex.ofReal_ne_zero.mpr (ne_of_gt (q.balanceFactor_pos i j hij)))
  change ‖(q.balanced i j hij).zVector‖ * ‖(q.balanced i j hij).wVector‖ = _ at hprod
  rw [← q.balanced_norms i j hij, ← sq] at hprod
  calc
    _ = Real.sqrt (‖(q.balanced i j hij).zVector‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := by rw [hprod]

noncomputable def ZWSystem.inverseScale {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) : ℂ := (‖q.zVector‖ : ℂ)⁻¹

theorem inverseScale_tendsto_zero {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass)
    (h : Tendsto (fun t => ‖(q t).zVector‖) atTop atTop) :
    Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0) := by
  have hh := (Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero.comp h)
  simpa [ZWSystem.inverseScale, Function.comp_def] using hh

theorem balanced_inverseScale_tendsto_zero {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j)
    (h : Tendsto (fun t => ‖(q t).zVector‖ * ‖(q t).wVector‖) atTop atTop) :
    Tendsto (fun t => ((q t).balanced i j hij).inverseScale) atTop (𝓝 0) := by
  apply inverseScale_tendsto_zero
  simpa only [ZWSystem.norm_balanced_eq_sqrt] using Real.tendsto_sqrt_atTop.comp h

/-- Build the common-scale limit directly from the two convergent normalized vectors. -/
noncomputable def normalizedZWLimit {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass)
    (hbal : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (vz vw : ColorCoordinate n → ℂ)
    (hz : Tendsto (fun t => unitNormalize (q t).zVector) atTop (𝓝 vz))
    (hw : Tendsto (fun t => unitNormalize (q t).wVector) atTop (𝓝 vw)) :
    ScaledZWLimit q (fun t => (q t).inverseScale) := by
  let zs := fun t => (q t).scaledZ (q t).inverseScale
  let ws := fun t => (q t).swap.scaledZ (q t).inverseScale
  have hzp (i : Fin n) : Tendsto (fun t => (zs t).position i) atTop (𝓝 (vz (.inl i))) :=
    ((continuous_apply (Sum.inl i : ColorCoordinate n)).tendsto vz).comp hz
  have hzf (i j : Fin n) : Tendsto (fun t => (zs t).force i j) atTop (𝓝 (vz (.inr (i, j)))) := by
    have h := ((continuous_apply (Sum.inr (i, j) : ColorCoordinate n)).tendsto vz).comp hz
    simpa only [unitNormalize, Pi.smul_apply, smul_eq_mul, ZWSystem.zVector,
      ZWSystem.inverseScale, ZWSystem.scaledZ, zs, mul_assoc] using h
  have hwp (i : Fin n) : Tendsto (fun t => (ws t).position i) atTop (𝓝 (vw (.inl i))) := by
    have h := ((continuous_apply (Sum.inl i : ColorCoordinate n)).tendsto vw).comp hw
    change Tendsto (fun t => (‖(q t).wVector‖ : ℂ)⁻¹ * (q t).w i) atTop _ at h
    simpa only [← hbal, ZWSystem.inverseScale, ZWSystem.scaledZ, ZWSystem.swap, ws] using h
  have hwf (i j : Fin n) : Tendsto (fun t => (ws t).force i j) atTop (𝓝 (vw (.inr (i, j)))) := by
    have h := ((continuous_apply (Sum.inr (i, j) : ColorCoordinate n)).tendsto vw).comp hw
    change Tendsto (fun t => (‖(q t).wVector‖ : ℂ)⁻¹ *
      ((q t).delta i j ^ 3 * ((q t).w i - (q t).w j))) atTop _ at h
    simpa only [← hbal, ZWSystem.inverseScale, ZWSystem.scaledZ, ZWSystem.swap, ws, mul_assoc] using h
  exact {
    z := OneColorLimit.ofLimit zs (fun i => vz (.inl i)) (fun i j => vz (.inr (i, j))) hzp hzf
    w := OneColorLimit.ofLimit ws (fun i => vw (.inl i)) (fun i j => vw (.inr (i, j))) hwp hwf
    z_position := hzp
    w_position := hwp
    z_force := fun i j => by simpa only [zs, ZWSystem.scaledZ, ZWSystem.zForce, mul_assoc] using hzf i j
    w_force := fun i j => by simpa only [ws, ZWSystem.swap, ZWSystem.scaledZ, ZWSystem.wForce, mul_assoc] using hwf i j
  }

def OneColorLimit.Nonzero {n : ℕ} {mass : Fin n → ℂ} (l : OneColorLimit ℂ n mass) : Prop :=
  (∃ i, l.position i ≠ 0) ∨ (∃ i j, l.force i j ≠ 0)

theorem norm_one_vector_nonzero {n : ℕ} (v : ColorCoordinate n → ℂ) (hv : ‖v‖ = 1) :
    (∃ i, v (.inl i) ≠ 0) ∨ (∃ i j, v (.inr (i, j)) ≠ 0) := by
  classical
  by_contra hn
  have hz : v = 0 := by
    funext c
    rcases c with i | ⟨i, j⟩
    · by_contra h
      exact hn (Or.inl ⟨i, h⟩)
    · by_contra h
      exact hn (Or.inr ⟨i, j, h⟩)
  rw [hz, norm_zero] at hv
  exact zero_ne_one hv

/-- The common subsequence and both actual leading limits are retained in the output. -/
structure ExtractedZWLimit {n : ℕ} {mass : Fin n → ℂ} (q : ℕ → ZWSystem ℂ n mass) where
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  leading : ScaledZWLimit (fun t => q (subsequence t))
    (fun t => (q (subsequence t)).inverseScale)
  z_nonzero : leading.z.Nonzero
  w_nonzero : leading.w.Nonzero

theorem exists_extractedZWLimit {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass)
    (hbal : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j : Fin n) (hij : i ≠ j) : Nonempty (ExtractedZWLimit q) := by
  obtain ⟨vz, vw, hvz, hvw, φ, hφ, hz, hw⟩ := exists_simultaneous_normalized_subsequence
    (fun t => (q t).zVector) (fun t => (q t).wVector)
    (fun t => (q t).zVector_ne_zero i j hij) (fun t => (q t).swap.zVector_ne_zero i j hij)
  let l := normalizedZWLimit (fun t => q (φ t)) (fun t => hbal (φ t)) vz vw hz hw
  exact ⟨{
    subsequence := φ
    strictMono := hφ
    leading := l
    z_nonzero := norm_one_vector_nonzero vz hvz
    w_nonzero := norm_one_vector_nonzero vw hvw
  }⟩

/-- Section 2.3: divergent norm product yields an extracted, balanced two-color
limit with a common scale tending to zero. Singularity before this hypothesis
and algebraic finiteness are treated in the corresponding extraction modules. -/
theorem exists_balanced_singular_limit {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j)
    (hprod : Tendsto (fun t => ‖(q t).zVector‖ * ‖(q t).wVector‖) atTop atTop) :
    ∃ l : ExtractedZWLimit (fun t => (q t).balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).balanced i j hij).inverseScale) atTop (𝓝 0) := by
  obtain ⟨l⟩ := exists_extractedZWLimit (fun t => (q t).balanced i j hij)
    (fun t => (q t).balanced_norms i j hij) i j hij
  exact ⟨l, (balanced_inverseScale_tendsto_zero q i j hij hprod).comp l.strictMono.tendsto_atTop⟩

end CentralConfigurations
