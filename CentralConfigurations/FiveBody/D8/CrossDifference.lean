import CentralConfigurations.FiveBody.D8.ScaleRatios
import CentralConfigurations.FiveBody.D8.UnequalResponse
import CentralConfigurations.FiveBody.D8.EqualResponse

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology

theorem cross_difference_identity {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass)
    (U : ℂ) (hm : mass 2+mass 3≠0) (hU : U≠0)
    (hcu : mass 4*U^3= -(mass 2+mass 3)) :
    crossW q 2-crossW q 3=(mass 2+mass 3)*upperR q-
      (mass 2+mass 3)*q.delta 2 3^3*upperR q*(rowW1 q U-rowW2 q U) := by
  have hE := upper_force_equations q U hm hU hcu
  have hR : q.w 2-q.w 3=(mass 2+mass 3)*upperR q := by dsimp [upperR]; field_simp [hm]
  linear_combination -hE.2.2.1+hE.2.2.2+hR

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
  {U : ℂ} (hUn : U≠0)
  (hU : Tendsto (fun t => (q t).delta 2 4/(q t).delta 2 3) atTop (𝓝 U))
  (hV : Tendsto (fun t => (q t).delta 3 4/(q t).delta 2 3) atTop (𝓝 U))
  (hshape : U^2*(m 2:ℂ)*m 3=((m 2:ℂ)+m 3)^2)
  (hcu : (m 4:ℂ)*U^3= -((m 2:ℂ)+m 3))
  (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include l hm hd hUn hU hV hshape hcu hb ha

theorem actual_cross_difference_small :
    (fun t => crossW (q t) 2-crossW (q t) 3) =o[atTop] (fun t => crossScale (q t)) := by
  by_cases heq : m 2=m 3
  · have hr := upper_r_small_cross l hm hd ha (equal_s_bounded l hm hd hUn hU hV hshape hcu heq ha)
    have hD := (equal_row_differences l hm hd hUn hU hV hshape hcu heq).2
    have hi := ((isBigO_refl (fun t => ((m 2:ℂ)+m 3)*(q t).delta 2 3^3*upperR (q t)) atTop).mul hD).trans_isLittleO
      (quadratic_internal_small_cross l hm hd hb ha)
    exact ((hr.const_mul_left ((m 2:ℂ)+m 3)).sub hi).congr_left
      (fun t => (cross_difference_identity (q t) U (upper_mass_ne l hm hd) hUn hcu).symm)
  · have hr := upper_r_small_cross l hm hd ha (unequal_s_bounded l hm hd hUn hU hV hshape hcu heq)
    have hE := (weighted_difference_expansions l hm hd hUn hU hV hshape).2.2
    have hsz := response_size_zero l hm hd hUn hU hV hshape
    have hss : (fun t => responseSize (q t)^2) =O[atTop] (fun t => responseSize (q t)) := by
      simpa only [pow_two] using D6.order_mul_bounded (isBigO_refl (fun t => responseSize (q t)) atTop) (hsz.isBigO_one ℂ)
    have hD : (fun t => rowW1 (q t) U-rowW2 (q t) U) =O[atTop] (fun t => (q t).inverseScale*upperS (q t)) := by
      have h := (hE.trans hss).add ((response_bounds q).1.const_mul_left
        ((3/2:ℂ)*((m 2:ℂ)/m 3-(m 3:ℂ)/m 2)))
      exact (h.congr_left (fun t => by ring)).trans (unequal_size_order l hm hd hUn hU hV hshape hcu heq)
    have hpref : (fun t => ((m 2:ℂ)+m 3)*(q t).delta 2 3^3*upperR (q t)*((q t).inverseScale*upperS (q t)))
        =O[atTop] (fun t => upperR (q t)) := by
      have h := D6.order_mul_bounded (isBigO_refl (fun t => upperR (q t)) atTop)
        ((upper_scale_limit l hm hd).isBigO_one ℂ |>.const_mul_left ((m 2:ℂ)+m 3))
      exact h.congr_left (fun t => by ring)
    have hi := (((isBigO_refl (fun t => ((m 2:ℂ)+m 3)*(q t).delta 2 3^3*upperR (q t)) atTop).mul hD).trans hpref).trans_isLittleO hr
    exact ((hr.const_mul_left ((m 2:ℂ)+m 3)).sub hi).congr_left
      (fun t => (cross_difference_identity (q t) U (upper_mass_ne l hm hd) hUn hcu).symm)

omit hUn hU hV hshape hcu in
theorem actual_mass_equalities : m 2=m 3 ∧ m 0=m 1 ∧ m 4=m 2/4 := by
  obtain ⟨U,hUn,hshape,hcu,φ,hφ,hU,hV,-⟩ := exists_upper_common_phase l hm hd
  have hd' : (l.comp φ hφ.tendsto_atTop).diagramCode=fiveBodySourceDiagram 6 := hd
  have hcross := actual_cross_difference_small (l.comp φ hφ.tendsto_atTop) hm hd' hUn hU hV hshape hcu
    (fun t => hb (φ t)) (ha.comp hφ.tendsto_atTop)
  obtain ⟨heq,hab⟩ := mass_equalities_of_cross_difference (l.comp φ hφ.tendsto_atTop) hm hd' hcross
  refine ⟨heq,hab,?_⟩
  have hp : (m 2:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 2)
  have hU2 : U^2=4 := by
    apply (mul_right_cancel₀ (pow_ne_zero 2 hp))
    rw [← heq] at hshape
    linear_combination hshape
  have he : (m 4:ℂ)^2*64=4*(m 2:ℂ)^2 := by
    have hh := congrArg (fun z : ℂ => z^2) hcu
    rw [← heq] at hh
    have hU6 : U^6=64 := by calc
      U^6=(U^2)^3 := by ring
      _=64 := by rw [hU2]; norm_num
    simp only [mul_pow,← pow_mul,hU6] at hh
    linear_combination hh
  have hr : m 4^2*64=4*m 2^2 := by exact_mod_cast he
  have hp0 := hm 2
  have hc0 := hm 4
  nlinarith

end CentralConfigurations.FiveBody.D8
