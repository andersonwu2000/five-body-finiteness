import CentralConfigurations.FiveBody.D2Regular.GaugeExtraction

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I : ℂ}

theorem triple_short_center_limit (s : ActualLimit m q l I) : Tendsto
    (fun t => tripleCenter (fun i => (m i:ℂ)) (q (s.subsequence t)).z /
      (q (s.subsequence t)).inverseScale) atTop (𝓝 0) := by
  have hc := s.triangle.mass_center_z
  simp [Fin.sum_univ_succ] at hc
  have hh := ((((s.triangle_z_limit 0).const_mul (m 0:ℂ)).add
    ((s.triangle_z_limit 1).const_mul (m 1:ℂ))).add
    ((s.triangle_z_limit 2).const_mul (m 2:ℂ))).div_const (tripleMass (fun i => (m i:ℂ)))
  have hz : (m 0:ℂ)*s.triangle.z 0+m 1*s.triangle.z 1+m 2*s.triangle.z 2=0 := by
    linear_combination hc
  rw [hz,zero_div] at hh
  apply hh.congr
  intro t
  dsimp [tripleCenter]
  ring

theorem triple_long_center_limit (s : ActualLimit m q l I) : Tendsto
    (fun t => (q (s.subsequence t)).inverseScale *
      tripleCenter (fun i => (m i:ℂ)) (q (s.subsequence t)).w) atTop (𝓝 0) := by
  have hh := ((l.w_position 2).comp s.strictMono.tendsto_atTop).sub (selected_extent_limit s)
  have hw : s.triangle.w 2=l.w.position 2 := s.triangle_w_eq 2
  rw [← hw,sub_self] at hh
  apply hh.congr
  intro t
  dsimp
  ring

namespace GaugeExtraction
variable {s : ActualLimit m q l I} (e : GaugeExtraction s) (hm : ∀ i, 0<m i)

theorem c_limit (i : Fin 3) : Tendsto (fun t => (e.chart hm t).c i) atTop
    (𝓝 (s.triangle.w 2*s.triangle.z i)) := by
  have hh := ((e.rotation_limit.mul (((s.triangle_z_limit i).sub
    (triple_short_center_limit s)).comp e.strictMono.tendsto_atTop)).div e.ratio_limit e.ratio_ne)
  simp only [sub_zero] at hh
  have hc : (e.ratio*s.triangle.w 2*s.triangle.z i)/e.ratio=
      s.triangle.w 2*s.triangle.z i := by field_simp [e.ratio_ne]
  rw [hc] at hh
  apply hh.congr
  intro t
  dsimp [chart,ReciprocalGauge.chart,ReciprocalGauge.normalized,ZWSystem.rescale,ActualChart.c]
  rw [tripleCenter_smul]
  field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
    (s.subsequence (e.select t)),(e.gauge t).time_ne]

theorem d_limit (i : Fin 3) : Tendsto (fun t => (e.chart hm t).d i) atTop
    (𝓝 (s.triangle.w i/s.triangle.w 2)) := by
  have hi : Tendsto (fun t => (q (s.subsequence t)).inverseScale*
      ((q (s.subsequence t)).w (tripleIndex i)-
        tripleCenter (fun j => (m j:ℂ)) (q (s.subsequence t)).w))
      atTop (𝓝 (s.triangle.w i)) := by
    have h := ((l.w_position (tripleIndex i)).comp s.strictMono.tendsto_atTop).sub
      (triple_long_center_limit s)
    rw [← s.triangle_w_eq i,sub_zero] at h
    simpa only [mul_sub] using h
  have hh := (e.ratio_limit.mul (hi.comp e.strictMono.tendsto_atTop)).div
    e.rotation_limit e.rotation_limit_ne
  have hc : (e.ratio*s.triangle.w i)/(e.ratio*s.triangle.w 2)=
      s.triangle.w i/s.triangle.w 2 := by field_simp [e.ratio_ne,s.w_ne_zero 2]
  rw [hc] at hh
  apply hh.congr
  intro t
  dsimp [chart,ReciprocalGauge.chart,ReciprocalGauge.normalized,ZWSystem.rescale,ActualChart.d]
  rw [tripleCenter_smul]
  field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
    (s.subsequence (e.select t)),(e.gauge t).time_ne]

theorem beta_limit : Tendsto (fun t => (e.chart hm t).beta) atTop
    (𝓝 ((s.pairW 1-s.pairW 0)/(pairMass (fun i => (m i:ℂ))*
      (e.ratio*s.triangle.w 2)*e.ratio))) := by
  have hA : pairMass (fun i => (m i:ℂ))≠0 := by
    change (m 3:ℂ)+m 4≠0
    exact_mod_cast ne_of_gt (add_pos (hm 3) (hm 4))
  have hh := (((s.pair_w_limit 1).sub (s.pair_w_limit 0)).comp e.strictMono.tendsto_atTop).div
    ((e.rotation_limit.const_mul (pairMass (fun i => (m i:ℂ)))).mul e.ratio_limit)
    (mul_ne_zero (mul_ne_zero hA e.rotation_limit_ne) e.ratio_ne)
  apply hh.congr
  intro t
  dsimp [chart,ReciprocalGauge.chart,ReciprocalGauge.normalized,ZWSystem.rescale,ActualChart.beta]
  field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
    (s.subsequence (e.select t)),(e.gauge t).time_ne,(e.gauge t).rotation_ne hA,hA]

theorem triangle_delta_limit (i j : Fin 3) :
    Tendsto (fun t => (e.chart hm t).point.delta (tripleIndex i) (tripleIndex j))
      atTop (𝓝 (s.triangle.delta i j)) :=
  (s.triangle_delta_limit i j).comp e.strictMono.tendsto_atTop

theorem pair_delta_limit : Tendsto (fun t => (e.chart hm t).point.delta 3 4)
    atTop (𝓝 s.pairDelta) := s.pair_delta_limit.comp e.strictMono.tendsto_atTop

end GaugeExtraction
end
end CentralConfigurations.FiveBody.D2.Regular
