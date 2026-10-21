import CentralConfigurations.FiveBody.D8.ResponseOrders
import CentralConfigurations.FiveBody.D8.Absorption

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology

theorem unequal_response_coefficient {p q : ℝ} (hp : 0<p) (hq : 0<q) (hne : p≠q) :
    3*(q:ℂ)/(2*p)-3*(p:ℂ)/(2*q)≠0 := by
  have hpn : (p:ℂ)≠0 := by exact_mod_cast ne_of_gt hp
  have hqn : (q:ℂ)≠0 := by exact_mod_cast ne_of_gt hq
  intro he
  field_simp [hpn,hqn] at he
  have hr : 3*(q^2-p^2)=q*2*p*0 := by exact_mod_cast he
  apply hne
  nlinarith

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
  {U : ℂ} (hUn : U≠0)
  (hU : Tendsto (fun t => (q t).delta 2 4/(q t).delta 2 3) atTop (𝓝 U))
  (hV : Tendsto (fun t => (q t).delta 3 4/(q t).delta 2 3) atTop (𝓝 U))
  (hshape : U^2*(m 2:ℂ)*m 3=((m 2:ℂ)+m 3)^2)
  (hcu : (m 4:ℂ)*U^3= -((m 2:ℂ)+m 3)) (hne : m 2≠m 3)
include l hm hd hUn hU hV hshape hcu hne

theorem unequal_size_order :
    (fun t => responseSize (q t)) =O[atTop] (fun t => (q t).inverseScale*upperS (q t)) := by
  obtain ⟨h1,h2,-⟩ := row_expansions l hm hd hUn hU hV hshape
  obtain ⟨hf,hg⟩ := row_z_orders l hm hd hUn hcu
  exact linear_two_response (unequal_response_coefficient (hm 2) (hm 3) hne)
    (upper_x_zero l hm hd) (upper_y_zero l hm hd hUn hU hshape) hf hg h1 h2

theorem unequal_remainder_small :
    (fun t => responseSize (q t)^2) =o[atTop] (fun t => (q t).inverseScale*upperS (q t)) := by
  have h0 := (isLittleO_one_iff ℂ).2 (response_size_zero l hm hd hUn hU hV hshape)
  simpa only [pow_two,one_mul] using h0.mul_isBigO (unequal_size_order l hm hd hUn hU hV hshape hcu hne)

theorem unequal_x_limit :
    Tendsto (fun t => upperX (q t)/((q t).inverseScale*upperS (q t))) atTop
      (𝓝 (-3/((3/2:ℂ)*((m 3:ℂ)/m 2-(m 2:ℂ)/m 3))*
        (((m 2:ℂ)+m 3)/l.z.force 2 3))) := by
  let d : ℂ := (3/2:ℂ)*((m 3:ℂ)/m 2-(m 2:ℂ)/m 3)
  have dn : d≠0 := by
    have he : d=3*(m 3:ℂ)/(2*m 2)-3*(m 2:ℂ)/(2*m 3) := by dsimp [d]; ring
    rw [he]
    exact unequal_response_coefficient (hm 2) (hm 3) hne
  obtain ⟨hT,hD,-⟩ := weighted_difference_expansions l hm hd hUn hU hV hshape
  have hrem := unequal_remainder_small l hm hd hUn hU hV hshape hcu hne
  have hT' := hT.trans_isLittleO hrem
  have hD' := hD.trans_isLittleO hrem
  have ha2 : (fun t => (q t).inverseScale^2) =o[atTop] (fun t => (q t).inverseScale*upperS (q t)) := by
    simpa only [pow_two] using (isBigO_refl (fun t => (q t).inverseScale) atTop).mul_isLittleO (inverseScale_small_s l hm hd)
  have hT0 := (weighted_row_z_order l hm hd hUn hcu).trans_isLittleO ha2
  have hlin : (fun t => upperX (q t)+3*upperY (q t)) =o[atTop] (fun t => (q t).inverseScale*upperS (q t)) := by
    apply ((hT0.sub hT').const_mul_left (2/((m 2:ℂ)+m 3))).congr_left
    intro t; field_simp [upper_mass_ne l hm hd]; ring
  have hdy : (fun t => d*upperY (q t)-((q t).delta 2 3)⁻¹^3) =o[atTop]
      (fun t => (q t).inverseScale*upperS (q t)) := by
    exact ((difference_row_z_asymptotic l hm hd hUn hcu).sub hD').congr_left (fun t => by dsimp [d]; ring)
  have hx : (fun t => upperX (q t)+(3/d)*((q t).delta 2 3)⁻¹^3) =o[atTop]
      (fun t => (q t).inverseScale*upperS (q t)) := by
    apply (hlin.sub (hdy.const_mul_left (3/d))).congr_left
    intro t; field_simp [dn]; ring
  have hlimit := hx.tendsto_div_nhds_zero.sub ((upper_inverse_cube_scale l hm hd).const_mul (3/d))
  convert hlimit using 1
  · ext t; ring
  · dsimp [d]; ring

theorem unequal_s_bounded : (fun t => upperS (q t)) =O[atTop] (fun _ => (1:ℂ)) := by
  have hn := l.z_force_ne_zero_of_code hd 2 3 (by decide) (by decide +kernel)
  have dn : (3/2:ℂ)*((m 3:ℂ)/m 2-(m 2:ℂ)/m 3)≠0 := by
    have he : (3/2:ℂ)*((m 3:ℂ)/m 2-(m 2:ℂ)/m 3)=3*(m 3:ℂ)/(2*m 2)-3*(m 2:ℂ)/(2*m 3) := by ring
    rw [he]
    exact unequal_response_coefficient (hm 2) (hm 3) hne
  have hvn : -3/((3/2:ℂ)*((m 3:ℂ)/m 2-(m 2:ℂ)/m 3))*(((m 2:ℂ)+m 3)/l.z.force 2 3)≠0 :=
    mul_ne_zero (div_ne_zero (by norm_num) dn) (div_ne_zero (upper_mass_ne l hm hd) hn)
  have hrev := isBigO_of_div_tendsto_nhds_of_ne_zero (unequal_x_limit l hm hd hUn hU hV hshape hcu hne) hvn
  have h := hrev.trans (upper_x_bigO l hm hd)
  have h2 := h.mul (isBigO_refl (fun t => upperS (q t)/(q t).inverseScale) atTop)
  have hs2 : (fun t => upperS (q t)^2) =O[atTop] (fun _ => (1:ℂ)^2) := by
    apply h2.congr
    · intro t; field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t]
    · intro t; field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t,upperS_ne (q t) (upper_mass_ne l hm hd)]
  exact hs2.of_pow (by decide : 2≠0)

end CentralConfigurations.FiveBody.D8
