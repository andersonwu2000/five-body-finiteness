import CentralConfigurations.FiveBody.D2EllZero.RootSigns

namespace CentralConfigurations.FiveBody.D2.EllZero
set_option maxHeartbeats 2000000

theorem root_ne_zero {u U w : ℂ} (hu : u^2*(-(U*w))=1) : u ≠ 0 := by
  intro h
  simp [h] at hu

theorem root_norm_equation {u U w : ℂ} (hu : u^2*(-(U*w))=1) :
    ‖u‖^2*‖U‖*‖w‖=1 := by
  have h := congrArg norm hu
  simpa [norm_mul,norm_pow,mul_assoc] using h

theorem normalized_root_bounds {U : ℂ} {w u : Fin 3 → ℂ} (hU : U ≠ 0)
    (hw : ∀ i, w i ≠ 0) (hu : ∀ i, u i^2*(-(U*w i))=1)
    (hout : ‖w 0‖^2=‖w 2‖^2) (hheavy : 8*‖w 1‖^2=‖w 0‖^2) :
    ‖u 0/u 0‖=1 ∧ ‖u 2/u 0‖=1 ∧ 6 < ‖5*(u 1/u 0)‖ := by
  have hu0 := root_ne_zero (hu 0)
  have hnU : ‖U‖ ≠ 0 := norm_ne_zero_iff.mpr hU
  have hn0 : ‖u 0‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
  have hnw0 : ‖w 0‖ ≠ 0 := norm_ne_zero_iff.mpr (hw 0)
  have hnw1 : 0 < ‖w 1‖ := norm_pos_iff.mpr (hw 1)
  have hnorm (i : Fin 3) := root_norm_equation (hu i)
  have hw02 : ‖w 0‖=‖w 2‖ := (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hout
  have hroot02 : ‖u 0‖=‖u 2‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    apply mul_right_cancel₀ (mul_ne_zero hnU hnw0)
    have h2 := hnorm 2
    rw [← hw02] at h2
    linear_combination hnorm 0-h2
  have hbalance : ‖u 1‖^2*‖w 1‖=‖u 0‖^2*‖w 0‖ := by
    apply mul_left_cancel₀ hnU
    linear_combination hnorm 1-hnorm 0
  have hratio : (‖u 1‖/‖u 0‖)^2=‖w 0‖/‖w 1‖ := by
    field_simp [hn0,ne_of_gt hnw1]
    linear_combination hbalance
  have hwratio : 2*‖w 1‖ < ‖w 0‖ := by
    by_contra h
    have hle : ‖w 0‖ ≤ 2*‖w 1‖ := le_of_not_gt h
    have hs := mul_self_le_mul_self (norm_nonneg _) hle
    have hp := sq_pos_of_pos hnw1
    nlinarith
  have hr2 : 2 < (‖u 1‖/‖u 0‖)^2 := by
    rw [hratio]
    exact (lt_div_iff₀ hnw1).mpr hwratio
  have hr : (6/5 : ℝ) < ‖u 1‖/‖u 0‖ := by
    apply (sq_lt_sq₀ (by norm_num) (div_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    linarith
  refine ⟨by simp [hu0],?_,?_⟩
  · rw [norm_div,← hroot02,div_self hn0]
  · rw [norm_mul,norm_div]
    norm_num
    linarith

end CentralConfigurations.FiveBody.D2.EllZero
