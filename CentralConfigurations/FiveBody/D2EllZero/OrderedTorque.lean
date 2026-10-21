import CentralConfigurations.FiveBody.D2EllZero.MetricBounds

namespace CentralConfigurations.FiveBody.D2.EllZero
open Exceptional
set_option maxHeartbeats 3000000

/-- Original six-root metric and unsquared torque rejection for the centered 1:5:1 family. -/
theorem false_of_ordered_pair_triangle_torque {p q a : ℝ}
    (hp : 0 < p) (hq : 0 < q) (ha : 0 < a) {U V : ℂ} (hU : U ≠ 0)
    {w u v : Fin 3 → ℂ} (hw : ∀ i, w i ≠ 0)
    (hbalance : (p : ℂ)*U+(q : ℂ)*V=0)
    (hu : ∀ i, u i^2*(-(U*w i))=1) (hv : ∀ i, v i^2*(-(V*w i))=1)
    (hout : ‖w 0‖^2=‖w 2‖^2) (hheavy : 8*‖w 1‖^2=‖w 0‖^2)
    (htorque : (p : ℂ)*a*(u 0+5*u 1+u 2)+(q : ℂ)*a*(v 0+5*v 1+v 2)=0) : False := by
  obtain ⟨ρ,hρ,_,ε,hε,he⟩ := exists_cross_signs hp hq hU hw hbalance hu hv
  obtain ⟨hn0,hn2,hnheavy⟩ := normalized_root_bounds hU hw hu hout hheavy
  let h : ℂ := 5*(u 1/u 0)
  let A : ℂ := u 0/u 0+u 2/u 0
  let C : ℂ := ε 0*(u 0/u 0)+ε 2*(u 2/u 0)
  have hA : ‖A‖ ≤ 2 := by
    have h := norm_add_le (u 0/u 0) (u 2/u 0)
    dsimp [A]
    rw [hn0,hn2] at h
    norm_num at h
    exact h
  have hεnorm (i : Fin 3) : ‖ε i‖=1 := by
    rcases hε i with h | h <;> rw [h] <;> simp
  have hC : ‖C‖ ≤ 2 := by
    have h := norm_add_le (ε 0*(u 0/u 0)) (ε 2*(u 2/u 0))
    dsimp [C]
    rw [norm_mul,norm_mul,hεnorm 0,hεnorm 2,hn0,hn2] at h
    norm_num at h
    exact h
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hq
  have hρC : (ρ : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hρ
  have hu0 := root_ne_zero (hu 0)
  have hT : (p : ℂ)*(u 0+5*u 1+u 2)+(q : ℂ)*(v 0+5*v 1+v 2)=0 := by
    apply mul_left_cancel₀ haC
    linear_combination htorque
  have hN : ((p/(q*ρ) : ℝ) : ℂ)*(h+A)+Complex.I*(ε 1*h+C)=0 := by
    rw [he 0,he 1,he 2] at hT
    dsimp [h,A,C]
    push_cast
    field_simp [hu0,hqC,hρC]
    linear_combination hT
  apply false_of_signed_heavy_torque (σ := 1) (τ := ε 1) (t := p/(q*ρ))
    (Or.inl rfl) (hε 1) hnheavy hA hC
  simpa using hN

end CentralConfigurations.FiveBody.D2.EllZero
