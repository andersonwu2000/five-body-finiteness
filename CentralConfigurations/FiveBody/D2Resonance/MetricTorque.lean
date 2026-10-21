import CentralConfigurations.FiveBody.D2Resonance.CenteredGeometry
import CentralConfigurations.FiveBody.D2EllZero.MetricBounds

namespace CentralConfigurations.FiveBody.D2.Resonance
open Exceptional EllZero
set_option maxHeartbeats 3000000

theorem resonance_root_bounds {U : ℂ} {w u : Fin 3 → ℂ} (hU : U≠0)
    (hw : ∀i, w i≠0) (hu : ∀i, u i^2*(-(U*w i))=1)
    (hout : ‖w 0‖^2=‖w 2‖^2) (hheavy : 4*‖w 1‖^2<‖w 0‖^2)
    (k : ℝ) (hk : 0<k) (hk2 : 18<k^2) :
    ‖u 0/u 0‖=1 ∧ ‖u 2/u 0‖=1 ∧ 6<‖(k:ℂ)*(u 1/u 0)‖ := by
  have hu0 := root_ne_zero (hu 0)
  have hnU : ‖U‖≠0 := norm_ne_zero_iff.mpr hU
  have hn0 : ‖u 0‖≠0 := norm_ne_zero_iff.mpr hu0
  have hnw0 : ‖w 0‖≠0 := norm_ne_zero_iff.mpr (hw 0)
  have hnw1 : 0<‖w 1‖ := norm_pos_iff.mpr (hw 1)
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
  have hwratio : 2*‖w 1‖<‖w 0‖ := by
    apply (sq_lt_sq₀ (by positivity) (norm_nonneg _)).mp
    nlinarith
  have hr2 : 2<(‖u 1‖/‖u 0‖)^2 := by
    rw [hratio]
    exact (lt_div_iff₀ hnw1).mpr hwratio
  have hkpos : 0<k^2 := sq_pos_of_pos hk
  have hproduct : 36<k^2*(‖u 1‖/‖u 0‖)^2 := by
    have h := mul_lt_mul_of_pos_left hr2 hkpos
    linarith
  refine ⟨by simp [hu0],?_,?_⟩
  · rw [norm_div,← hroot02,div_self hn0]
  · apply (sq_lt_sq₀ (by norm_num) (norm_nonneg _)).mp
    rw [norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hk,mul_pow]
    simpa only [show (6:ℝ)^2=36 by norm_num] using hproduct

theorem false_of_ordered_resonance_torque {p q a : ℝ}
    (hp : 0<p) (hq : 0<q) (ha : 0<a) {U V : ℂ} (hU : U≠0)
    {w u v : Fin 3 → ℂ} (hw : ∀i, w i≠0)
    (hbalance : (p:ℂ)*U+(q:ℂ)*V=0)
    (hu : ∀i, u i^2*(-(U*w i))=1) (hv : ∀i, v i^2*(-(V*w i))=1)
    (hout : ‖w 0‖^2=‖w 2‖^2) (hheavy : 4*‖w 1‖^2<‖w 0‖^2)
    (htorque : (p:ℂ)*a*(u 0+(resonanceWeight:ℂ)*u 1+u 2)+
      (q:ℂ)*a*(v 0+(resonanceWeight:ℂ)*v 1+v 2)=0) : False := by
  obtain ⟨ρ,hρ,_,ε,hε,he⟩ := exists_cross_signs hp hq hU hw hbalance hu hv
  obtain ⟨hn0,hn2,hnheavy⟩ := resonance_root_bounds hU hw hu hout hheavy
    resonanceWeight resonanceWeight_pos resonanceWeight_sq
  let h : ℂ := (resonanceWeight:ℂ)*(u 1/u 0)
  let A : ℂ := u 0/u 0+u 2/u 0
  let C : ℂ := ε 0*(u 0/u 0)+ε 2*(u 2/u 0)
  have hA : ‖A‖≤2 := by
    have h := norm_add_le (u 0/u 0) (u 2/u 0)
    dsimp [A]
    rw [hn0,hn2] at h
    norm_num at h
    exact h
  have hεnorm (i : Fin 3) : ‖ε i‖=1 := by
    rcases hε i with h | h <;> rw [h] <;> simp
  have hC : ‖C‖≤2 := by
    have h := norm_add_le (ε 0*(u 0/u 0)) (ε 2*(u 2/u 0))
    dsimp [C]
    rw [norm_mul,norm_mul,hεnorm 0,hεnorm 2,hn0,hn2] at h
    norm_num at h
    exact h
  have haC : (a:ℂ)≠0 := by exact_mod_cast ne_of_gt ha
  have hqC : (q:ℂ)≠0 := by exact_mod_cast ne_of_gt hq
  have hρC : (ρ:ℂ)≠0 := by exact_mod_cast ne_of_gt hρ
  have hu0 := root_ne_zero (hu 0)
  have hT : (p:ℂ)*(u 0+(resonanceWeight:ℂ)*u 1+u 2)+
      (q:ℂ)*(v 0+(resonanceWeight:ℂ)*v 1+v 2)=0 := by
    apply mul_left_cancel₀ haC
    linear_combination htorque
  have hN : ((p/(q*ρ):ℝ):ℂ)*(h+A)+Complex.I*(ε 1*h+C)=0 := by
    rw [he 0,he 1,he 2] at hT
    dsimp [h,A,C]
    push_cast
    field_simp [hu0,hqC,hρC]
    linear_combination hT
  apply false_of_signed_heavy_torque (σ:=1) (τ:=ε 1) (t:=p/(q*ρ))
    (Or.inl rfl) (hε 1) hnheavy hA hC
  simpa using hN

end CentralConfigurations.FiveBody.D2.Resonance
