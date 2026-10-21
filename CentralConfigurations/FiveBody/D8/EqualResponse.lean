import CentralConfigurations.FiveBody.D8.ResponseOrders
import CentralConfigurations.FiveBody.D8.Absorption

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
  {U : ℂ} (hUn : U≠0)
  (hU : Tendsto (fun t => (q t).delta 2 4/(q t).delta 2 3) atTop (𝓝 U))
  (hV : Tendsto (fun t => (q t).delta 3 4/(q t).delta 2 3) atTop (𝓝 U))
  (hshape : U^2*(m 2:ℂ)*m 3=((m 2:ℂ)+m 3)^2)
  (hcu : (m 4:ℂ)*U^3= -((m 2:ℂ)+m 3)) (heq : m 2=m 3)
include l hm hd hUn hU hV hshape hcu heq

theorem equal_size_order :
    (fun t => responseSize (q t)) =O[atTop] (fun t => (q t).inverseScale/upperS (q t)) := by
  have ha2 : (fun t => (q t).inverseScale^2) =O[atTop] (fun t => (q t).inverseScale/upperS (q t)) := by
    have h := D6.order_mul_bounded (isBigO_refl (fun t => (q t).inverseScale/upperS (q t)) atTop)
      ((upper_s_scaled_zero l hm hd).isBigO_one ℂ)
    apply h.congr_left
    intro t; field_simp [upperS_ne (q t) (upper_mass_ne l hm hd)]
  have hT := (weighted_row_z_order l hm hd hUn hcu).trans ha2
  have hE := (weighted_difference_expansions l hm hd hUn hU hV hshape).1
  have hE' : (fun t => (m 2:ℂ)*rowZ1 (q t) U+m 3*rowZ2 (q t) U-
      ((m 2:ℂ)*upperX (q t)+(3*(m 2:ℂ))*upperY (q t))) =O[atTop] (fun t => responseSize (q t)^2) := by
    apply hE.congr_left
    intro t; rw [heq]; ring
  exact linear_one_response (mul_ne_zero (by norm_num) (by exact_mod_cast ne_of_gt (hm 2)))
    (upper_x_zero l hm hd) (upper_y_zero l hm hd hUn hU hshape)
    (upper_x_bigO l hm hd) hT hE'

theorem equal_row_differences :
    (fun t => rowZ1 (q t) U-rowZ2 (q t) U) =O[atTop] (fun t => ((q t).inverseScale/upperS (q t))^2) ∧
    (fun t => rowW1 (q t) U-rowW2 (q t) U) =O[atTop] (fun t => ((q t).inverseScale/upperS (q t))^2) := by
  obtain ⟨-,hD,hW⟩ := weighted_difference_expansions l hm hd hUn hU hV hshape
  have hsize := (equal_size_order l hm hd hUn hU hV hshape hcu heq).pow 2
  constructor
  · simpa only [heq,sub_self,mul_zero,zero_mul,sub_zero] using hD.trans hsize
  · simpa only [heq,sub_self,mul_zero,zero_mul,sub_zero] using hW.trans hsize

theorem equal_s_cubic_order :
    (fun t => upperS (q t)^3) =O[atTop] (fun t => (q t).inverseScale) := by
  have hn := l.z_force_ne_zero_of_code hd 2 3 (by decide) (by decide +kernel)
  have hlim : Tendsto (fun t => (rowZ1 (q t) U-rowZ2 (q t) U)/((q t).inverseScale*upperS (q t))) atTop
      (𝓝 (((m 2:ℂ)+m 3)/l.z.force 2 3)) := by
    have h := (difference_row_z_asymptotic l hm hd hUn hcu).tendsto_div_nhds_zero.add (upper_inverse_cube_scale l hm hd)
    rw [zero_add] at h
    exact h.congr (fun t => by ring)
  have hrev := isBigO_of_div_tendsto_nhds_of_ne_zero hlim (div_ne_zero (upper_mass_ne l hm hd) hn)
  have ho := hrev.trans (equal_row_differences l hm hd hUn hU hV hshape hcu heq).1
  have h := ho.mul (isBigO_refl (fun t => upperS (q t)^2/(q t).inverseScale) atTop)
  apply h.congr
  · intro t; field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t]
  · intro t; field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t,upperS_ne (q t) (upper_mass_ne l hm hd)]

theorem equal_s_bounded (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    (fun t => upperS (q t)) =O[atTop] (fun _ => (1:ℂ)) := by
  have h := (equal_s_cubic_order l hm hd hUn hU hV hshape hcu heq).trans (ha.isBigO_one ℂ)
  have hh : (fun t => upperS (q t)^3) =O[atTop] (fun _ => (1:ℂ)^3) := by simpa using h
  exact hh.of_pow (by decide : 3≠0)

end CentralConfigurations.FiveBody.D8
