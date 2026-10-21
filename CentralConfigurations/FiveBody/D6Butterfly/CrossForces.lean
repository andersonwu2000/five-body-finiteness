import CentralConfigurations.FiveBody.D6Butterfly.WingEquations

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

theorem cross_force_orders (e : Fin 4) :
    (fun t => (g t).normalized.zForce (crossLeft e) (crossRight e)) =O[atTop] (fun t => (g t).time^2) ∧
    (fun t => (g t).normalized.wForce (crossLeft e) (crossRight e)) =O[atTop] (fun t => (g t).time^2) := by
  have ht := time_scale l g (long_separations l hm hd).1 (long_separations l hm hd).2
  have hδ := bigO_one_of_bounded_range (bounded_range_div_of_bigO ((cross_delta_bigO l hm hd e).trans ht.2))
  obtain ⟨hz,hw⟩ := leading_positions l hm hd g hb ha
  have hs (f : ℕ → Fin 5 → ℂ) (h : ∀ i, (fun t => (g t).time*f t i) =O[atTop] (fun _ => (1:ℂ))) :
      (fun t => (q t).delta (crossLeft e) (crossRight e)^3*(f t (crossLeft e)-f t (crossRight e))) =O[atTop]
        (fun t => (g t).time^2) := by
    have hbd := (hδ.pow 3).mul ((h (crossLeft e)).sub (h (crossRight e)))
    have hh := (isBigO_refl (fun t => (g t).time^2) atTop).mul hbd
    simp only [one_pow,mul_one] at hh
    apply hh.congr_left
    intro t
    field_simp [(g t).time_ne]
  exact ⟨hs (fun t i => (g t).normalized.z i) (fun i => (hz i).isBigO_one ℂ),
    hs (fun t i => (g t).normalized.w i) (fun i => (hw i).isBigO_one ℂ)⟩

theorem cross_sum_orders :
    (fun t => (g t).crossZ) =O[atTop] (fun t => (g t).time^2) ∧
    (fun t => (g t).crossW) =O[atTop] (fun t => (g t).time^2) := by
  have hz0 := (cross_force_orders l hm hd g hb ha 0).1
  have hz1 := (cross_force_orders l hm hd g hb ha 2).1
  have hw0 := (cross_force_orders l hm hd g hb ha 0).2
  have hw1 := (cross_force_orders l hm hd g hb ha 1).2
  constructor
  · apply ((hz0.const_mul_left (-(m 0:ℂ))).add (hz1.const_mul_left (-(m 1:ℂ)))).congr_left
    intro t
    change -(m 0:ℂ)*(g t).normalized.zForce 0 3+ -(m 1:ℂ)*(g t).normalized.zForce 1 3=_
    simp only [PairGauge.crossZ,(g t).normalized.zForce_antisymm 3 0,(g t).normalized.zForce_antisymm 3 1]
    ring
  · exact (hw0.const_mul_left (m 3:ℂ)).add (hw1.const_mul_left (m 4:ℂ))

end CentralConfigurations.FiveBody.D6
