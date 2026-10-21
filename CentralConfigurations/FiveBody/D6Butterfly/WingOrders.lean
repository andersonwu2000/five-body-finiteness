import CentralConfigurations.FiveBody.D6Butterfly.CrossForces
import CentralConfigurations.FiveBody.D6Butterfly.WingRigidity

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

theorem bounded_mul {f g : ℕ → ℂ}
    (hf : f =O[atTop] (fun _ => (1:ℂ))) (hg : g =O[atTop] (fun _ => (1:ℂ))) :
    (fun t => f t*g t) =O[atTop] (fun _ => (1:ℂ)) := by
  simpa only [mul_one] using hf.mul hg

theorem order_mul_bounded {f g a : ℕ → ℂ}
    (hf : f =O[atTop] a) (hg : g =O[atTop] (fun _ => (1:ℂ))) :
    (fun t => f t*g t) =O[atTop] a := by
  simpa only [mul_one] using hf.mul hg

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (g : ∀ t, PairGauge (q t))
  (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include l hm hd hb ha

theorem wing_residuals :
    (fun t => (q t).delta 2 3^3-(q t).delta 2 4^3) =O[atTop] (fun t => (g t).time^2) ∧
    (fun t => (q t).delta 0 2^3-(q t).delta 1 2^3) =O[atTop] (fun t => (g t).time^2) ∧
    (fun t => 2*(m 3:ℂ)*(q t).delta 3 4^3+m 2*(q t).delta 2 3^3-1) =O[atTop] (fun t => (g t).time^2) ∧
    (fun t => 2*(m 0:ℂ)*(q t).delta 0 1^3+m 2*(q t).delta 0 2^3-1) =O[atTop] (fun t => (g t).time^2) ∧
    (fun t => ((q t).delta 3 4)⁻¹^2-2*((q t).delta 2 3)⁻¹^2-2*((q t).delta 2 4)⁻¹^2) =O[atTop] (fun t => (g t).time^2) ∧
    (fun t => ((q t).delta 0 1)⁻¹^2-2*((q t).delta 0 2)⁻¹^2-2*((q t).delta 1 2)⁻¹^2) =O[atTop] (fun t => (g t).time^2) := by
  have C (i : Fin 8) := bigO_one_of_bounded_range (coefficient_bounds l hm hd g hb ha i)
  have B (e : Fin 6) : (fun t => (q t).delta (wingLeft e) (wingRight e)^3) =O[atTop] (fun _ => (1:ℂ)) := by
    obtain ⟨u,-,hu⟩ := wing_cube_limits l hm hd e
    exact hu.isBigO_one ℂ
  have T := isBigO_refl (fun t => (g t).time^2) atTop
  have ht := (time_zero l g (long_separations l hm hd).1 (long_separations l hm hd).2 ha).isBigO_one ℂ
  obtain ⟨hZ,hW⟩ := cross_sum_orders l hm hd g hb ha
  have hTZ : (fun t => (g t).time*(g t).crossZ) =O[atTop] (fun t => (g t).time^2) := by
    simpa only [one_mul] using ht.mul hZ
  have hTW : (fun t => (g t).time*(g t).crossW) =O[atTop] (fun t => (g t).time^2) := by
    simpa only [one_mul] using ht.mul hW
  obtain ⟨hm01,hm34⟩ := l.five_body_source19_mass_relation hm hb ha hd
  have hn3 : (m 3:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 3)
  have hn0 : (m 0:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 0)
  constructor
  · have he := (((bounded_mul ((B 1).const_mul_left (m 0:ℂ)) ((C 4).sub (C 2))).add
      (bounded_mul ((B 2).const_mul_left (m 1:ℂ)) ((C 4).sub (C 3)))).add
      (bounded_mul (((B 3).const_mul_left (m 3:ℂ)).add ((B 4).const_mul_left (m 4:ℂ)))
        ((C 4).sub (C 0)))).sub (C 4)
    have hh := (order_mul_bounded T he).const_mul_left (m 3:ℂ)⁻¹
    apply hh.congr_left
    intro t
    dsimp [wingLeft,wingRight]
    rw [← (g t).wing_difference_z,← hm34]
    field_simp [hn3]
  constructor
  · have he := (((bounded_mul ((B 3).const_mul_left (m 3:ℂ)) ((C 5).sub (C 6))).add
      (bounded_mul ((B 4).const_mul_left (m 4:ℂ)) ((C 5).sub (C 7)))).add
      (bounded_mul (((B 1).const_mul_left (m 0:ℂ)).add ((B 2).const_mul_left (m 1:ℂ)))
        ((C 5).sub (C 1)))).sub (C 5)
    have hh := (order_mul_bounded T he).const_mul_left (m 0:ℂ)⁻¹
    apply hh.congr_left
    intro t
    dsimp [wingLeft,wingRight]
    rw [← (g t).wing_difference_w,← hm01]
    field_simp [hn0]
  constructor
  · have he := (C 0).sub (bounded_mul ((B 3).const_mul_left (m 2:ℂ)) ((C 0).sub (C 4)))
    apply ((order_mul_bounded T he).sub hTZ).congr_left
    intro t
    dsimp [wingLeft,wingRight]
    rw [← (g t).wing_normalization_z,← hm34]
  constructor
  · have he := (C 1).sub (bounded_mul ((B 1).const_mul_left (m 2:ℂ)) ((C 1).sub (C 5)))
    apply ((order_mul_bounded T he).sub hTW).congr_left
    intro t
    dsimp [wingLeft,wingRight]
    rw [← (g t).wing_normalization_w,← hm01]
  constructor
  · have he := bounded_mul ((C 0).sub (C 4)) (((C 6).add (C 7)).sub ((C 5).const_mul_left 2))
    apply ((order_mul_bounded T he).const_mul_left (-2)).congr_left
    intro t
    rw [(g t).wing_closure_z]
    ring
  · have he := bounded_mul ((C 1).sub (C 5)) (((C 2).add (C 3)).sub ((C 4).const_mul_left 2))
    apply ((order_mul_bounded T he).const_mul_left (-2)).congr_left
    intro t
    rw [(g t).wing_closure_w]
    ring

theorem wing_cube_orders {u : Fin 6 → ℂ}
    (hu : ∀ e, Tendsto (fun t => (q t).delta (wingLeft e) (wingRight e)) atTop (𝓝 (u e)))
    (hun : ∀ e, u e≠0) (e : Fin 6) :
    (fun t => (q t).delta (wingLeft e) (wingRight e)^3-u e^3) =O[atTop] (fun t => (g t).time^2) := by
  obtain ⟨hdz,hdw,hnz,hnw,hcz,hcw⟩ := wing_residuals l hm hd g hb ha
  have ht : Tendsto (fun t => (g t).time^2) atTop (𝓝 0) := by
    simpa using (time_zero l g (long_separations l hm hd).1 (long_separations l hm hd).2 ha).pow 2
  obtain ⟨hzr,hzf,hzg⟩ := wing_rigidity (hun 5) (hun 3) (hun 4) (hu 5) (hu 3) (hu 4) ht hdz hnz hcz
  obtain ⟨hwr,hwf,hwg⟩ := wing_rigidity (hun 0) (hun 1) (hun 2) (hu 0) (hu 1) (hu 2) ht hdw hnw hcw
  fin_cases e
  · exact hwr
  · exact hwf
  · exact hwg
  · exact hzf
  · exact hzg
  · exact hzr

end CentralConfigurations.FiveBody.D6

