import CentralConfigurations.FiveBody.D8.CrossDifference
import CentralConfigurations.FiveBody.PairEnergyInertia

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology BigOperators

theorem pivot_inertia {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) :
    q.toNormalized.potential= -(∑ i, mass i)*q.z 4*q.w 4+
      mass 0*(q.z 0-q.z 4)*(q.w 0-q.w 4)+mass 1*(q.z 1-q.z 4)*(q.w 1-q.w 4)+
      mass 2*(q.z 2-q.z 4)*(q.w 2-q.w 4)+mass 3*(q.z 3-q.z 4)*(q.w 3-q.w 4) := by
  rw [PairEnergy.zw_potential]
  have hz := q.mass_center_z
  have hw := q.mass_center_w
  simp [Fin.sum_univ_succ] at hz hw ⊢
  linear_combination q.w 4*hz+q.z 4*hw

theorem metric_inverse_square {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) (i j : Fin 5) (hij : i≠j) :
    (q.z i-q.z j)*(q.w i-q.w j)=(q.delta i j)⁻¹^2 := by
  field_simp [q.delta_ne_zero i j hij]
  linear_combination q.distance i j hij

theorem full_metric_inertia {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) :
    q.toNormalized.potential= -(∑ i, mass i)*q.z 4*q.w 4+
      mass 0*(q.delta 0 4)⁻¹^2+mass 1*(q.delta 1 4)⁻¹^2+
      mass 2*(q.delta 2 4)⁻¹^2+mass 3*(q.delta 3 4)⁻¹^2 := by
  have h := pivot_inertia q
  simp only [mul_assoc] at h
  rw [metric_inverse_square q 0 4 (by decide),metric_inverse_square q 1 4 (by decide),
    metric_inverse_square q 2 4 (by decide),metric_inverse_square q 3 4 (by decide)] at h
  simpa only [mul_assoc] using h

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
include l hm hd

theorem centroid_product_zero : Tendsto (fun t => (q t).z 4*(q t).w 4) atTop (𝓝 0) := by
  have hW : Tendsto (fun t => (q t).inverseScale*(q t).w 4) atTop (𝓝 0) := by
    simpa only [(leading_positions l hm hd).2.2.2.1] using l.w_position 4
  exact ((lower_small_z l hm hd).2.2.mul (isBigO_refl (fun t => (q t).w 4) atTop)).trans_tendsto hW

theorem upper_base_inverse_zero : Tendsto (fun t => ((q t).delta 2 3)⁻¹) atTop (𝓝 0) := by
  apply tendsto_zero_of_complex_power (by decide : 3≠0)
  have h := (upper_inverse_cube_scale l hm hd).mul (upper_s_scaled_zero l hm hd)
  rw [mul_zero] at h
  apply h.congr
  intro t
  exact div_mul_cancel₀ _ (mul_ne_zero (ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t)
    (upperS_ne (q t) (upper_mass_ne l hm hd)))

theorem upper_inverse_zero {U : ℂ} (hUn : U≠0)
    (hU : Tendsto (fun t => (q t).delta 2 4/(q t).delta 2 3) atTop (𝓝 U))
    (hV : Tendsto (fun t => (q t).delta 3 4/(q t).delta 2 3) atTop (𝓝 U)) :
    Tendsto (fun t => ((q t).delta 2 4)⁻¹) atTop (𝓝 0) ∧
    Tendsto (fun t => ((q t).delta 3 4)⁻¹) atTop (𝓝 0) := by
  have h0 := upper_base_inverse_zero l hm hd
  constructor
  · have h := (hU.inv₀ hUn).mul h0
    rw [mul_zero] at h
    apply h.congr
    intro t
    field_simp [(q t).delta_ne_zero 2 3 (by decide),(q t).delta_ne_zero 2 4 (by decide)]
  · have h := (hV.inv₀ hUn).mul h0
    rw [mul_zero] at h
    apply h.congr
    intro t
    field_simp [(q t).delta_ne_zero 2 3 (by decide),(q t).delta_ne_zero 3 4 (by decide)]

/-- The complete finite invariant: the central product and both upper metric
terms are independently controlled before taking the lower-wing limit. -/
theorem retained_lower_energy {I0 : ℝ}
    (hI : ∀ t, (q t).toNormalized.potential=(I0:ℂ))
    {U F G : ℂ} (hUn : U≠0) (hFn : F≠0) (hGn : G≠0)
    (hU : Tendsto (fun t => (q t).delta 2 4/(q t).delta 2 3) atTop (𝓝 U))
    (hV : Tendsto (fun t => (q t).delta 3 4/(q t).delta 2 3) atTop (𝓝 U))
    (hF : Tendsto (fun t => (q t).delta 0 4) atTop (𝓝 F))
    (hG : Tendsto (fun t => (q t).delta 1 4) atTop (𝓝 G)) :
    (I0:ℂ)=(m 0:ℂ)*F⁻¹^2+m 1*G⁻¹^2 := by
  obtain ⟨h24,h34⟩ := upper_inverse_zero l hm hd hUn hU hV
  have hc := (centroid_product_zero l hm hd).const_mul (-(∑ i, (m i:ℂ)))
  have hlim := (((hc.add (((hF.inv₀ hFn).pow 2).const_mul (m 0:ℂ))).add
    (((hG.inv₀ hGn).pow 2).const_mul (m 1:ℂ))).add ((h24.pow 2).const_mul (m 2:ℂ))).add
    ((h34.pow 2).const_mul (m 3:ℂ))
  simp only [zero_pow (by decide : 2≠0),mul_zero,zero_add,add_zero] at hlim
  have he : Tendsto (fun _ : ℕ => (I0:ℂ)) atTop (𝓝 ((m 0:ℂ)*F⁻¹^2+m 1*G⁻¹^2)) := by
    apply hlim.congr
    intro t
    have hh := full_metric_inertia (q t)
    rw [hI t] at hh
    simpa only [mul_assoc] using hh.symm
  exact tendsto_nhds_unique tendsto_const_nhds he

end CentralConfigurations.FiveBody.D8
