import CentralConfigurations.FiveBody.D2Regular.GaugeLimits
import CentralConfigurations.FiveBody.D2Regular.Centers

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I : ℂ}

/-- One further strict selection makes the actual gauge ratio converge.
Every signed root is still the original root on this same selected sequence. -/
structure GaugeExtraction (s : ActualLimit m q l I) where
  select : ℕ → ℕ
  strictMono : StrictMono select
  gauge : ∀ t, ReciprocalGauge (q (s.subsequence (select t)))
  ratio : ℂ
  ratio_ne : ratio≠0
  ratio_limit : Tendsto
    (fun t => (gauge t).time/(q (s.subsequence (select t))).inverseScale)
    atTop (𝓝 ratio)

theorem exists_gaugeExtraction (s : ActualLimit m q l I) (hm : ∀ i, 0<m i) :
    Nonempty (GaugeExtraction s) := by
  obtain ⟨N,⟨g⟩⟩ := exists_gauge_tail s hm
  let φ : ℕ → ℕ := fun t => N+t
  have hφ : StrictMono φ := by intro i j hij; dsimp [φ]; omega
  have hsq := gauge_time_ratio_square_limit s hm φ hφ g
  let f : ℕ → Unit → ℂ := fun t _ => (g t).time/(q (s.subsequence (φ t))).inverseScale
  have hb : ∀ u, Bornology.IsBounded (Set.range (fun t => f t u)) := by
    intro u
    exact bounded_of_power_tendsto (by decide : (2:ℕ)≠0) hsq
  obtain ⟨v,ψ,hψ,hv⟩ := exists_finite_coordinate_limits f hb
  have hv2 : v ()^2=pairMass (fun i => (m i:ℂ))/((s.pairZ 1-s.pairZ 0)*s.triangle.w 2) :=
    tendsto_nhds_unique ((hv ()).pow 2) (hsq.comp hψ.tendsto_atTop)
  have hn : v ()≠0 := by
    intro hz
    have hA : pairMass (fun i => (m i:ℂ))≠0 := by
      change (m 3:ℂ)+m 4≠0
      exact_mod_cast ne_of_gt (add_pos (hm 3) (hm 4))
    have hnn := div_ne_zero hA (mul_ne_zero (pair_difference_ne s hm) (s.w_ne_zero 2))
    apply hnn
    rw [← hv2,hz]
    norm_num
  exact ⟨⟨fun t => φ (ψ t),hφ.comp hψ,fun t => g (ψ t),v (),hn,hv ()⟩⟩

namespace GaugeExtraction
variable {s : ActualLimit m q l I} (e : GaugeExtraction s)

theorem time_zero : Tendsto (fun t => (e.gauge t).time) atTop (𝓝 0) := by
  have hh := e.ratio_limit.mul (s.scale_limit.comp e.strictMono.tendsto_atTop)
  rw [mul_zero] at hh
  apply hh.congr
  intro t
  dsimp only [Function.comp_apply]
  exact div_mul_cancel₀ _ (ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) _)

theorem rotation_limit : Tendsto (fun t => (e.gauge t).rotation) atTop
    (𝓝 (e.ratio*s.triangle.w 2)) := by
  have hh := e.ratio_limit.mul ((selected_extent_limit s).comp e.strictMono.tendsto_atTop)
  apply hh.congr
  intro t
  dsimp [ReciprocalGauge.rotation]
  field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
    (s.subsequence (e.select t))]

theorem rotation_limit_ne : e.ratio*s.triangle.w 2≠0 := mul_ne_zero e.ratio_ne (s.w_ne_zero 2)

def chart (hm : ∀ i, 0<m i) (t : ℕ) : ActualChart (fun i => (m i:ℂ)) :=
  (e.gauge t).chart (by
    change (m 3:ℂ)+m 4≠0
    exact_mod_cast ne_of_gt (add_pos (hm 3) (hm 4))) (by
    change (m 0:ℂ)+m 1+m 2≠0
    exact_mod_cast ne_of_gt (add_pos (add_pos (hm 0) (hm 1)) (hm 2)))

theorem chart_exact_scalar (hm : ∀ i, 0<m i) (t : ℕ) :
    (e.chart hm t).point.toNormalized.potential=I := s.exact_scalar (e.select t)

theorem cross_limit (hm : ∀ i, 0<m i) (p : Fin 2) (i : Fin 3) :
    Tendsto (fun t => (e.chart hm t).cross p i) atTop (𝓝 (s.cross p i/e.ratio)) := by
  have hh := ((s.cross_scaled_limit p i).comp e.strictMono.tendsto_atTop).div e.ratio_limit e.ratio_ne
  apply hh.congr
  intro t
  dsimp [chart,ReciprocalGauge.chart,ReciprocalGauge.normalized,ZWSystem.rescale,ActualChart.cross]
  field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
    (s.subsequence (e.select t)),(e.gauge t).time_ne]

end GaugeExtraction
end
end CentralConfigurations.FiveBody.D2.Regular
