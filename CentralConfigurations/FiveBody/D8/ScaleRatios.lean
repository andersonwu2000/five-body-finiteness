import CentralConfigurations.FiveBody.D8.CrossCompatibility

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology

theorem upperR_formula {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) (hm : mass 2+mass 3≠0) :
    upperR q=1/((mass 2+mass 3)^2*q.delta 2 3^2*upperS q) := by
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hm)
    (pow_ne_zero 2 (q.delta_ne_zero 2 3 (by decide)))) (upperS_ne q hm))).2
  linear_combination upper_base_metric q hm

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
include l hm hd

theorem upper_r_small_cross
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hs : (fun t => upperS (q t)) =O[atTop] (fun _ => (1:ℂ))) :
    (fun t => upperR (q t)) =o[atTop] (fun t => crossScale (q t)) := by
  have hA := upper_scale_limit l hm hd
  have hB := cross_delta_sq_scale l hm hd 2 0 (Or.inl rfl) (Or.inl rfl)
  have hAn := div_ne_zero (l.z_force_ne_zero_of_code hd 2 3 (by decide) (by decide +kernel)) (upper_mass_ne l hm hd)
  have hBn := inv_ne_zero (mul_ne_zero (cross_coefficient_ne l hm hd 2 0 (Or.inl rfl) (Or.inl rfl)).1
    (neg_ne_zero.mpr (cross_coefficient_ne l hm hd 2 0 (Or.inl rfl) (Or.inl rfl)).2))
  have hnum : Tendsto (fun t => (q t).inverseScale*upperS (q t)^7) atTop (𝓝 0) := by
    apply (isLittleO_one_iff ℂ).1
    simpa only [one_pow,one_mul] using ((isLittleO_one_iff ℂ).2 ha).mul_isBigO (hs.pow 7)
  have hlim := hnum.div ((((hA.pow 4).mul (hB.pow 3)).const_mul (((m 2:ℂ)+m 3)^12)))
    (mul_ne_zero (pow_ne_zero 12 (upper_mass_ne l hm hd)) (mul_ne_zero (pow_ne_zero 4 hAn) (pow_ne_zero 3 hBn)))
  rw [zero_div] at hlim
  have hpow : Tendsto (fun t => (upperR (q t)/crossScale (q t))^6) atTop (𝓝 0) := by
    apply hlim.congr
    intro t
    rw [upperR_formula (q t) (upper_mass_ne l hm hd)]
    dsimp [crossScale]
    field_simp [upper_mass_ne l hm hd,upperS_ne (q t) (upper_mass_ne l hm hd),
      (q t).delta_ne_zero 2 3 (by decide),(q t).delta_ne_zero 2 0 (by decide),
      ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t]
  apply (isLittleO_iff_tendsto' (Filter.Eventually.of_forall (fun t he => False.elim
    ((div_ne_zero ((q t).delta_ne_zero 2 0 (by decide)) (upperS_ne (q t) (upper_mass_ne l hm hd))) he)))).2
  exact tendsto_zero_of_complex_power (by decide : 6≠0) hpow

theorem quadratic_internal_small_cross
    (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    (fun t => ((m 2:ℂ)+m 3)*(q t).delta 2 3^3*upperR (q t)*((q t).inverseScale/upperS (q t))^2)
      =o[atTop] (fun t => crossScale (q t)) := by
  have hA := upper_scale_limit l hm hd
  have hB := cross_delta_sq_scale l hm hd 2 0 (Or.inl rfl) (Or.inl rfl)
  have hBn := inv_ne_zero (mul_ne_zero (cross_coefficient_ne l hm hd 2 0 (Or.inl rfl) (Or.inl rfl)).1
    (neg_ne_zero.mpr (cross_coefficient_ne l hm hd 2 0 (Or.inl rfl) (Or.inl rfl)).2))
  have heps : Tendsto (fun t => ((q t).epsilon:ℂ)) atTop (𝓝 0) := by
    have h := ZWSystem.epsilon_tendsto_zero_of_inverseScale (q := q) ha
    exact_mod_cast h
  have hquot := (epsilon_small_s l hm hd hb).tendsto_div_nhds_zero
  have hsmall : Tendsto (fun t => ((q t).epsilon:ℂ)^3*(((q t).epsilon:ℂ)/upperS (q t))^11) atTop (𝓝 0) := by
    simpa using (heps.pow 3).mul (hquot.pow 11)
  have hlim := ((hA.pow 2).mul hsmall).div ((hB.pow 3).const_mul (((m 2:ℂ)+m 3)^6))
    (mul_ne_zero (pow_ne_zero 6 (upper_mass_ne l hm hd)) (pow_ne_zero 3 hBn))
  rw [mul_zero,zero_div] at hlim
  have hpow : Tendsto (fun t => ((((m 2:ℂ)+m 3)*(q t).delta 2 3^3*upperR (q t)*
      ((q t).inverseScale/upperS (q t))^2)/crossScale (q t))^6) atTop (𝓝 0) := by
    apply hlim.congr
    intro t
    have hε : ((q t).epsilon:ℂ)^2=(q t).inverseScale := (q t).epsilon_sq_eq_inverseScale
    rw [upperR_formula (q t) (upper_mass_ne l hm hd)]
    dsimp [crossScale]
    field_simp [upper_mass_ne l hm hd,upperS_ne (q t) (upper_mass_ne l hm hd),
      (q t).delta_ne_zero 2 3 (by decide),(q t).delta_ne_zero 2 0 (by decide),
      ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t]
    have he := congrArg (fun z : ℂ => z^7) hε
    linear_combination he
  apply (isLittleO_iff_tendsto' (Filter.Eventually.of_forall (fun t he => False.elim
    ((div_ne_zero ((q t).delta_ne_zero 2 0 (by decide)) (upperS_ne (q t) (upper_mass_ne l hm hd))) he)))).2
  exact tendsto_zero_of_complex_power (by decide : 6≠0) hpow

end CentralConfigurations.FiveBody.D8
