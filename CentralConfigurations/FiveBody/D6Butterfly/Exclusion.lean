import CentralConfigurations.FiveBody.D6Butterfly.FinalTorque
import CentralConfigurations.FiveBody.PhysicalPotentialFloor

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (g : ∀ t, PairGauge (q t))
  (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include l hm hd hb ha

/-- The selected chart has only actual finite limits. Every correction rate,
wing catalogue, common translation, and torque remainder is derived above. -/
theorem false_of_chart_limits {u : Fin 6 → ℂ} {c : Fin 8 → ℂ} {h : Fin 4 → ℂ}
    (hu : ∀ e, Tendsto (fun t => (q t).delta (wingLeft e) (wingRight e)) atTop (𝓝 (u e)))
    (hun : ∀ e, u e≠0) (hc : ∀ i, Tendsto (fun t => (g t).coeff i) atTop (𝓝 (c i)))
    (hh : ∀ e, Tendsto (fun t => (g t).crossRoot e) atTop (𝓝 (h e))) : False := by
  have ht := time_zero l g (long_separations l hm hd).1 (long_separations l hm hd).2 ha
  have hj := all_translation_orders l hm hd g hb ha hu hun hc hh
  obtain ⟨hA,hB⟩ := internal_force_orders l hm hd g hb ha hu hun hc hh
  have hJ := reduced_torque_order l hm hd g hb ha hu hun hc hh
  change (fun t => reducedExpression (m 3) (m 0) (m 2) ((g t).coeff)
    (g t).internalW (g t).internalZ (g t).time (h 0) (h 2)) =O[atTop] (fun t => (g t).time^3) at hJ
  obtain ⟨h0,h1⟩ := leading_torque_coefficients ht (fun t => (g t).time_ne) hc hj hA hB hJ
  have hs := actual_wing_static l hm hd g hb ha hu hun hc hh
  have hH : h 0^2= -1 := (cross_root_rigidity l hm hd g hb ha 0 (hh 0)).1
  have hK : h 2^2=1 := (cross_root_rigidity l hm hd g hb ha 2 (hh 2)).1
  obtain ⟨hp0,hq0⟩ := zero_center_limits (hm 3) (hm 0) (hm 2) hs hun hH hK h0 h1
  have han : (m 3:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 3)
  have hbn : (m 0:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 0)
  have hC0 : torqueCoefficient c (h 0) (h 2)=0 := by
    simp only [firstTorqueCoefficient,hp0,hq0,mul_zero,zero_add,sub_zero,zero_sub,neg_eq_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_left (mul_ne_zero han hbn)
  have hA0 : (fun t => (g t).internalW) =O[atTop] (fun t => (g t).time^2) := by
    simpa only [hq0,mul_zero,sub_zero] using hA
  have hB0 : (fun t => (g t).internalZ) =O[atTop] (fun t => (g t).time^2) := by
    simpa only [hp0,mul_zero,sub_zero] using hB
  have hfinal := final_torque_coefficient ht (fun t => (g t).time_ne) hj hp0 hq0 hC0 hA0 hB0 hJ
  exact final_coefficient_nonzero (hm 3) (hm 0) (hm 2) hH hK hfinal

omit g in
/-- Actual balanced Chang diagram 19 (AK D6) is impossible for every positive
mass tuple. Signed inverse-distance sheets and arbitrary sequence rates are
retained. No fixed potential, physical floor, or generic-mass guard is used. -/
theorem false_of_chang19 : False := by
  let g' : ∀ t, PairGauge (q t) := fun t => pairGauge (q t)
  obtain ⟨c,u,h,φ,hφ,hc,hu,hun,hh,-,-⟩ := exists_chart_with_cross_orders l hm hd g' hb ha
  exact false_of_chart_limits (l.comp φ hφ.tendsto_atTop) hm hd (fun t => g' (φ t))
    (fun t => hb (φ t)) (ha.comp hφ.tendsto_atTop) hu hun hc hh

omit g in
/-- Same-invariant wrapper for the global five-body classification. The
source's D6 torque obstruction is stronger than the fixed-level claim. -/
theorem false_of_chang19_on_physical_level {I0 : ℝ}
    (_hphysical : PhysicalPotentialLevel m I0)
    (_hI : ∀ t, (q t).toNormalized.potential=(I0:ℂ)) : False :=
  false_of_chang19 l hm hd hb ha

end CentralConfigurations.FiveBody.D6
