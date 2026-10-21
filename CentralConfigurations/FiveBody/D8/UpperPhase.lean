import CentralConfigurations.FiveBody.D8.UpperLimits
import CentralConfigurations.FiveBody.D8.PhaseRigidity

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology

theorem upper_metric_cycle {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass)
    (hm : mass 2+mass 3≠0) :
    (q.delta 2 4/q.delta 2 3)^2*(q.delta 3 4/q.delta 2 3)^2*
      ((q.z 2-q.z 4)/upperS q)*((q.z 3-q.z 4)/upperS q)=
    (mass 2+mass 3)*((q.delta 3 4/q.delta 2 3)^2*((q.z 3-q.z 4)/upperS q)-
      (q.delta 2 4/q.delta 2 3)^2*((q.z 2-q.z 4)/upperS q)) := by
  have h23 := q.distance 2 3 (by decide)
  have h24 := q.distance 2 4 (by decide)
  have h34 := q.distance 3 4 (by decide)
  have he : q.delta 2 4^2*q.delta 3 4^2*(q.z 2-q.z 4)*(q.z 3-q.z 4)=
      q.delta 2 3^2*(q.z 2-q.z 3)*(q.delta 3 4^2*(q.z 3-q.z 4)-q.delta 2 4^2*(q.z 2-q.z 4)) := by
    linear_combination -q.delta 2 4^2*q.delta 3 4^2*(q.z 2-q.z 4)*(q.z 3-q.z 4)*h23+
      q.delta 2 3^2*(q.z 2-q.z 3)*q.delta 3 4^2*(q.z 3-q.z 4)*h24-
      q.delta 2 3^2*(q.z 2-q.z 3)*q.delta 2 4^2*(q.z 2-q.z 4)*h34
  dsimp [upperS]
  field_simp [q.delta_ne_zero 2 3 (by decide),q.z_separation_ne_zero (by decide : (2:Fin 5)≠3),hm]
  linear_combination he

theorem upper_w_ratio {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass)
    (hm : mass 2+mass 3≠0) :
    (q.w 2-q.w 4)/upperR q=(mass 2+mass 3)^2/
      ((q.delta 2 4/q.delta 2 3)^2*((q.z 2-q.z 4)/upperS q)) := by
  have h23 := q.distance 2 3 (by decide)
  have h24 := q.distance 2 4 (by decide)
  dsimp [upperS,upperR]
  field_simp [hm,q.delta_ne_zero 2 3 (by decide),q.delta_ne_zero 2 4 (by decide),
    q.z_separation_ne_zero (by decide : (2:Fin 5)≠3),q.z_separation_ne_zero (by decide : (2:Fin 5)≠4),
    q.w_separation_ne_zero (by decide : (2:Fin 5)≠3)]
  linear_combination h24-h23

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
include l hm hd

theorem upper_roots_metric {U V : ℂ}
    (hU : Tendsto (fun t => (q t).delta 2 4/(q t).delta 2 3) atTop (𝓝 U))
    (hV : Tendsto (fun t => (q t).delta 3 4/(q t).delta 2 3) atTop (𝓝 V)) :
    (m 2:ℂ)*m 3*U^2*V^2=((m 2:ℂ)+m 3)*((m 2:ℂ)*V^2+m 3*U^2) := by
  obtain ⟨hz2,hz3⟩ := upper_z_ratio_limits l hm hd
  have he := tendsto_nhds_unique (((hU.pow 2).mul (hV.pow 2)).mul hz2 |>.mul hz3)
    ((((hV.pow 2).mul hz3).sub ((hU.pow 2).mul hz2)).const_mul ((m 2:ℂ)+m 3) |>.congr
      (fun t => (upper_metric_cycle (q t) (upper_mass_ne l hm hd)).symm))
  linear_combination -he

theorem upper_y_zero {U : ℂ} (hUn : U≠0)
    (hU : Tendsto (fun t => (q t).delta 2 4/(q t).delta 2 3) atTop (𝓝 U))
    (hshape : U^2*(m 2:ℂ)*m 3=((m 2:ℂ)+m 3)^2) :
    Tendsto (fun t => upperY (q t)) atTop (𝓝 0) := by
  have hn3 : (m 3:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 3)
  have hr := (tendsto_const_nhds (x := ((m 2:ℂ)+m 3)^2)).div
    ((hU.pow 2).mul (upper_z_ratio_limits l hm hd).1) (mul_ne_zero (pow_ne_zero 2 hUn) hn3)
  have he : ((m 2:ℂ)+m 3)^2/(U^2*m 3)=(m 2:ℂ) := by
    apply (div_eq_iff (mul_ne_zero (pow_ne_zero 2 hUn) hn3)).2
    linear_combination -hshape
  rw [he] at hr
  have hr' := hr.congr (fun t => (upper_w_ratio (q t) (upper_mass_ne l hm hd)).symm)
  have hy := hr'.sub_const (m 2:ℂ)
  simp only [sub_self] at hy
  apply hy.congr
  intro t
  rw [(upper_coordinates (q t) (upper_mass_ne l hm hd)).2.2.1]
  field_simp [upperR_ne (q t) (upper_mass_ne l hm hd)]
  ring

theorem exists_upper_common_phase : ∃ U : ℂ, U≠0 ∧
    U^2*(m 2:ℂ)*m 3=((m 2:ℂ)+m 3)^2 ∧ (m 4:ℂ)*U^3= -((m 2:ℂ)+m 3) ∧
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun t => (q (φ t)).delta 2 4/(q (φ t)).delta 2 3) atTop (𝓝 U) ∧
      Tendsto (fun t => (q (φ t)).delta 3 4/(q (φ t)).delta 2 3) atTop (𝓝 U) ∧
      Tendsto (fun t => upperY (q (φ t))) atTop (𝓝 0) := by
  obtain ⟨U,V,hUn,hVn,φ,hφ,hU,hV,hUc,hVc⟩ := exists_upper_root_limits l hm hd
  have hd' : (l.comp φ hφ.tendsto_atTop).diagramCode=fiveBodySourceDiagram 6 := hd
  have he := upper_roots_metric (l.comp φ hφ.tendsto_atTop) hm hd' hU hV
  obtain ⟨hUV,hshape,hcube⟩ := upper_phase_rigidity (m 2) (m 3) (m 4) (hm 2) (hm 3) (hm 4) U V hUn hVn hUc hVc he
  subst V
  exact ⟨U,hUn,hshape,hcube,φ,hφ,hU,hV,upper_y_zero (l.comp φ hφ.tendsto_atTop) hm hd' hUn hU hshape⟩

end CentralConfigurations.FiveBody.D8
