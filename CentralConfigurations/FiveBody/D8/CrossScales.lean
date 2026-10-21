import CentralConfigurations.FiveBody.D8.UpperPhase
import CentralConfigurations.Asymptotics.OneStrokeClusterLimits

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology
noncomputable section

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
include l hm hd

def upperZCoefficient (m : Fin 5 → ℝ) (i : Fin 5) : ℂ := if i=2 then (m 3:ℂ) else -(m 2:ℂ)

theorem upper_z_absolute_ratio (i : Fin 5) (hi : i=2 ∨ i=3) :
    Tendsto (fun t => (q t).z i/upperS (q t)) atTop (𝓝 (upperZCoefficient m i)) := by
  have hz4 := ((lower_small_z l hm hd).2.2.trans_isLittleO (inverseScale_small_s l hm hd)).tendsto_div_nhds_zero
  obtain ⟨hz2,hz3⟩ := upper_z_ratio_limits l hm hd
  rcases hi with rfl | rfl
  · convert hz2.add hz4 using 1
    · ext t; ring
    · simp [upperZCoefficient]
  · convert hz3.add hz4 using 1
    · ext t; ring
    · simp [upperZCoefficient]

theorem cross_coordinate_limits (i j : Fin 5) (hi : i=2 ∨ i=3) (hj : j=0 ∨ j=1) :
    Tendsto (fun t => ((q t).z i-(q t).z j)/upperS (q t)) atTop (𝓝 (upperZCoefficient m i)) ∧
    Tendsto (fun t => (q t).inverseScale*((q t).w i-(q t).w j)) atTop (𝓝 (-l.w.position j)) := by
  have hzj : (fun t => (q t).z j) =O[atTop] (fun t => (q t).inverseScale) := by
    rcases hj with rfl | rfl
    · exact (lower_small_z l hm hd).1
    · exact (lower_small_z l hm hd).2.1
  have hzij := (upper_z_absolute_ratio l hm hd i hi).sub
    (hzj.trans_isLittleO (inverseScale_small_s l hm hd)).tendsto_div_nhds_zero
  have hwi : l.w.position i=0 := by
    rcases hi with rfl | rfl
    · exact (leading_positions l hm hd).2.1
    · exact (leading_positions l hm hd).2.2.1
  exact ⟨by simpa only [sub_div,sub_zero] using hzij,
    by simpa only [mul_sub,hwi,zero_sub] using (l.w_position i).sub (l.w_position j)⟩

theorem cross_coefficient_ne (i j : Fin 5) (hi : i=2 ∨ i=3) (hj : j=0 ∨ j=1) :
    upperZCoefficient m i≠0 ∧ l.w.position j≠0 := by
  constructor
  · rcases hi with rfl | rfl <;> dsimp [upperZCoefficient]
    · exact_mod_cast ne_of_gt (hm 3)
    · exact neg_ne_zero.mpr (by exact_mod_cast ne_of_gt (hm 2))
  · rcases hj with rfl | rfl
    · exact (leading_positions l hm hd).2.2.2.2.1
    · exact (leading_positions l hm hd).2.2.2.2.2.1

theorem cross_delta_sq_scale (i j : Fin 5) (hi : i=2 ∨ i=3) (hj : j=0 ∨ j=1) :
    Tendsto (fun t => (q t).delta i j^2/((q t).inverseScale/upperS (q t))) atTop
      (𝓝 ((upperZCoefficient m i*(-l.w.position j))⁻¹)) := by
  obtain ⟨hz,hw⟩ := cross_coordinate_limits l hm hd i j hi hj
  obtain ⟨hzi,hwj⟩ := cross_coefficient_ne l hm hd i j hi hj
  have hij : i≠j := by rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> decide
  have h := (hz.mul hw).inv₀ (mul_ne_zero hzi (neg_ne_zero.mpr hwj))
  apply h.congr
  intro t
  have hdij := (q t).distance i j hij
  field_simp [upperS_ne (q t) (upper_mass_ne l hm hd),
    ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t,
    (q t).z_separation_ne_zero hij,(q t).w_separation_ne_zero hij]
  linear_combination -hdij

theorem cross_delta_zero (i j : Fin 5) (hi : i=2 ∨ i=3) (hj : j=0 ∨ j=1) :
    Tendsto (fun t => (q t).delta i j) atTop (𝓝 0) := by
  apply tendsto_zero_of_complex_power (by decide : 2≠0)
  have h := (cross_delta_sq_scale l hm hd i j hi hj).mul (inverseScale_small_s l hm hd).tendsto_div_nhds_zero
  rw [mul_zero] at h
  apply h.congr
  intro t
  exact div_mul_cancel₀ _ (div_ne_zero
    (ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t)
    (upperS_ne (q t) (upper_mass_ne l hm hd)))

theorem cross_zForce_small (i j : Fin 5) (hi : i=2 ∨ i=3) (hj : j=0 ∨ j=1) :
    (fun t => (q t).zForce i j) =o[atTop] (fun t => (q t).inverseScale) := by
  obtain ⟨-,hw⟩ := cross_coordinate_limits l hm hd i j hi hj
  have hwj := (cross_coefficient_ne l hm hd i j hi hj).2
  have h := (cross_delta_zero l hm hd i j hi hj).div hw (neg_ne_zero.mpr hwj)
  rw [zero_div] at h
  apply (isLittleO_iff_tendsto' (Filter.Eventually.of_forall
    (fun t he => False.elim (ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t he)))).2
  apply h.congr
  intro t
  have hij : i≠j := by rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> decide
  have hdij := (q t).distance i j hij
  dsimp [ZWSystem.zForce]
  field_simp [(q t).w_separation_ne_zero hij,
    ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t]
  linear_combination -(q t).delta i j*hdij

theorem upper_scale_limit :
    Tendsto (fun t => (q t).inverseScale*upperS (q t)*(q t).delta 2 3^3) atTop
      (𝓝 (l.z.force 2 3/((m 2:ℂ)+m 3))) := by
  have h := (l.z_force 2 3).div_const ((m 2:ℂ)+m 3)
  exact h.congr (fun t => by dsimp [ZWSystem.zForce,upperS]; ring)

theorem upper_inverse_cube_scale :
    Tendsto (fun t => ((q t).delta 2 3)⁻¹^3/((q t).inverseScale*upperS (q t))) atTop
      (𝓝 (((m 2:ℂ)+m 3)/l.z.force 2 3)) := by
  have hn := l.z_force_ne_zero_of_code hd 2 3 (by decide) (by decide +kernel)
  have h := (upper_scale_limit l hm hd).inv₀ (div_ne_zero hn (upper_mass_ne l hm hd))
  simpa only [inv_div,mul_inv,inv_pow,div_eq_mul_inv,mul_comm,mul_left_comm,inv_inv] using h

end
end CentralConfigurations.FiveBody.D8
