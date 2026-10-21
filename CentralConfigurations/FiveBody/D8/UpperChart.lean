import CentralConfigurations.FiveBody.D8.Support

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology
noncomputable section

variable {mass : Fin 5 → ℂ}

def upperS (q : ZWSystem ℂ 5 mass) : ℂ := (q.z 2-q.z 3)/(mass 2+mass 3)
def upperR (q : ZWSystem ℂ 5 mass) : ℂ := (q.w 2-q.w 3)/(mass 2+mass 3)
def upperX (q : ZWSystem ℂ 5 mass) : ℂ := ((mass 2*q.z 2+mass 3*q.z 3)/(mass 2+mass 3)-q.z 4)/upperS q
def upperY (q : ZWSystem ℂ 5 mass) : ℂ := ((mass 3*q.w 2+mass 2*q.w 3)/(mass 2+mass 3)-q.w 4)/upperR q

theorem upperS_ne (q : ZWSystem ℂ 5 mass) (hm : mass 2+mass 3≠0) : upperS q≠0 :=
  div_ne_zero (q.z_separation_ne_zero (by decide : (2:Fin 5)≠3)) hm
theorem upperR_ne (q : ZWSystem ℂ 5 mass) (hm : mass 2+mass 3≠0) : upperR q≠0 :=
  div_ne_zero (q.w_separation_ne_zero (by decide : (2:Fin 5)≠3)) hm

theorem upper_coordinates (q : ZWSystem ℂ 5 mass) (hm : mass 2+mass 3≠0) :
    q.z 2=q.z 4+upperS q*(mass 3+upperX q) ∧
    q.z 3=q.z 4+upperS q*(upperX q-mass 2) ∧
    q.w 2=q.w 4+upperR q*(mass 2+upperY q) ∧
    q.w 3=q.w 4+upperR q*(upperY q-mass 3) := by
  have hs := upperS_ne q hm
  have hr := upperR_ne q hm
  have hsz : (mass 2+mass 3)*upperS q=q.z 2-q.z 3 := by dsimp [upperS]; field_simp [hm]
  have hrw : (mass 2+mass 3)*upperR q=q.w 2-q.w 3 := by dsimp [upperR]; field_simp [hm]
  dsimp only [upperX,upperY]
  refine ⟨?_,?_,?_,?_⟩ <;> field_simp [hs,hr,hm]
  · linear_combination -mass 3*hsz
  · linear_combination mass 2*hsz
  · linear_combination -mass 2*hrw
  · linear_combination mass 3*hrw

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
include l hm hd

theorem upper_mass_ne : (m 2:ℂ)+m 3≠0 := by exact_mod_cast ne_of_gt (add_pos (hm 2) (hm 3))

theorem inverseScale_small_s :
    (fun t => (q t).inverseScale) =o[atTop] (fun t => upperS (q t)) := by
  have h := (inverseScale_small_upper l hm hd).const_mul_right (inv_ne_zero (upper_mass_ne l hm hd))
  simpa only [upperS,div_eq_mul_inv,mul_comm] using h

theorem epsilon_small_s (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖) :
    (fun t => ((q t).epsilon:ℂ)) =o[atTop] (fun t => upperS (q t)) := by
  have h := (epsilon_small_upper l hm hd hb).const_mul_right (inv_ne_zero (upper_mass_ne l hm hd))
  simpa only [upperS,div_eq_mul_inv,mul_comm] using h

theorem upper_x_numerator :
    (fun t => ((m 2:ℂ)*(q t).z 2+m 3*(q t).z 3)/((m 2:ℂ)+m 3)-(q t).z 4) =O[atTop]
      (fun t => (q t).inverseScale) := by
  have h := ((upper_weighted_z l hm hd).const_mul_left (((m 2:ℂ)+m 3)⁻¹)).sub (lower_small_z l hm hd).2.2
  exact h.congr_left (fun t => by ring)

theorem upper_x_bigO : (fun t => upperX (q t)) =O[atTop] (fun t => (q t).inverseScale/upperS (q t)) := by
  simpa only [upperX,div_eq_mul_inv] using (upper_x_numerator l hm hd).mul (isBigO_refl (fun t => (upperS (q t))⁻¹) atTop)

theorem upper_x_zero : Tendsto (fun t => upperX (q t)) atTop (𝓝 0) :=
  ((upper_x_numerator l hm hd).trans_isLittleO (inverseScale_small_s l hm hd)).tendsto_div_nhds_zero

theorem upper_s_scaled_zero : Tendsto (fun t => (q t).inverseScale*upperS (q t)) atTop (𝓝 0) := by
  have h := (upper_scaled_zero l hm hd).mul_const (((m 2:ℂ)+m 3)⁻¹)
  simpa only [upperS,div_eq_mul_inv,mul_assoc,zero_mul] using h

theorem upper_z_ratio_limits :
    Tendsto (fun t => ((q t).z 2-(q t).z 4)/upperS (q t)) atTop (𝓝 (m 3:ℂ)) ∧
    Tendsto (fun t => ((q t).z 3-(q t).z 4)/upperS (q t)) atTop (𝓝 (-(m 2:ℂ))) := by
  have hx := upper_x_zero l hm hd
  have hc t := upper_coordinates (q t) (upper_mass_ne l hm hd)
  constructor
  · convert (tendsto_const_nhds.add hx : Tendsto (fun t => (m 3:ℂ)+upperX (q t)) atTop (𝓝 ((m 3:ℂ)+0))) using 1
    · ext t
      rw [(hc t).1]
      field_simp [upperS_ne (q t) (upper_mass_ne l hm hd)]
      ring
    · simp
  · convert (hx.sub_const (m 2:ℂ)) using 1
    · ext t
      rw [(hc t).2.1]
      field_simp [upperS_ne (q t) (upper_mass_ne l hm hd)]
      ring
    · simp

end
end CentralConfigurations.FiveBody.D8

