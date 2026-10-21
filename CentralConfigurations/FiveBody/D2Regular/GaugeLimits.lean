import CentralConfigurations.FiveBody.D2Regular.Chart
import CentralConfigurations.FiveBody.D6Butterfly.Gauge

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I : ℂ}
  (s : ActualLimit m q l I)

theorem selected_extent_limit : Tendsto
    (fun t => (q (s.subsequence t)).inverseScale*
      ((q (s.subsequence t)).w 2-tripleCenter (fun i => (m i:ℂ)) (q (s.subsequence t)).w))
    atTop (𝓝 (s.triangle.w 2)) := by
  have hh (i : Fin 3) : Tendsto
      (fun t => (q (s.subsequence t)).inverseScale*(q (s.subsequence t)).w (tripleIndex i))
      atTop (𝓝 (s.triangle.w i)) := by
    rw [s.triangle_w_eq]
    exact (l.w_position (tripleIndex i)).comp s.strictMono.tendsto_atTop
  have hc := s.triangle.mass_center_w
  simp [Fin.sum_univ_succ] at hc
  have ht := (((hh 0).const_mul (m 0:ℂ)).add ((hh 1).const_mul (m 1:ℂ))).add
    ((hh 2).const_mul (m 2:ℂ))
  have hc' : (m 0:ℂ)*s.triangle.w 0+m 1*s.triangle.w 1+m 2*s.triangle.w 2=0 := by
    linear_combination hc
  rw [hc'] at ht
  have h := (hh 2).sub (ht.div_const (tripleMass (fun i => (m i:ℂ))))
  simp only [zero_div,sub_zero] at h
  apply h.congr
  intro t
  dsimp [tripleCenter,tripleIndex]
  ring

theorem selected_extent_eventually_ne : ∀ᶠ t in atTop,
    (q (s.subsequence t)).w 2-tripleCenter (fun i => (m i:ℂ)) (q (s.subsequence t)).w≠0 := by
  filter_upwards [((selected_extent_limit s).eventually_ne (s.w_ne_zero 2))] with t ht
  exact (mul_ne_zero_iff.mp ht).2

theorem exists_gauge_tail (hm : ∀ i, 0<m i) : ∃ N : ℕ,
    Nonempty (∀ t, ReciprocalGauge (q (s.subsequence (N+t)))) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp (selected_extent_eventually_ne s)
  refine ⟨N,⟨fun t => reciprocalGauge _ ?_ (hN (N+t) (Nat.le_add_right _ _))⟩⟩
  change (m 3:ℂ)+m 4≠0
  exact_mod_cast ne_of_gt (add_pos (hm 3) (hm 4))

theorem selected_pair_difference_limit : Tendsto
    (fun t => (q (s.subsequence t)).inverseScale*
      ((q (s.subsequence t)).z 4-(q (s.subsequence t)).z 3))
    atTop (𝓝 (s.pairZ 1-s.pairZ 0)) := by
  have h := ((l.z_position 4).sub (l.z_position 3)).comp s.strictMono.tendsto_atTop
  simpa only [s.pairZ_eq,mul_sub] using h

theorem pair_difference_ne (hm : ∀ i, 0<m i) : s.pairZ 1-s.pairZ 0≠0 := by
  intro hh
  have hz := sub_eq_zero.mp hh
  have hb := s.pair_balance
  rw [hz] at hb
  have hA : (m 3:ℂ)+m 4≠0 := by exact_mod_cast ne_of_gt (add_pos (hm 3) (hm 4))
  apply mul_ne_zero hA (s.pairZ_ne_zero 0)
  linear_combination hb

theorem gauge_time_ratio_square_limit (hm : ∀ i, 0<m i)
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (g : ∀ t, ReciprocalGauge (q (s.subsequence (φ t)))) :
    Tendsto (fun t => ((g t).time/(q (s.subsequence (φ t))).inverseScale)^2) atTop
      (𝓝 (pairMass (fun i => (m i:ℂ))/((s.pairZ 1-s.pairZ 0)*s.triangle.w 2))) := by
  have h := (tendsto_const_nhds : Tendsto
    (fun _ : ℕ => pairMass (fun i => (m i:ℂ))) atTop (𝓝 _)).div
    (((selected_pair_difference_limit s).comp hφ.tendsto_atTop).mul
      ((selected_extent_limit s).comp hφ.tendsto_atTop))
    (mul_ne_zero (pair_difference_ne s hm) (s.w_ne_zero 2))
  apply h.congr
  intro t
  dsimp only [Pi.div_apply,Function.comp_apply]
  rw [div_pow,(g t).time_square]
  field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) (s.subsequence (φ t)),
    (q (s.subsequence (φ t))).z_separation_ne_zero (by decide : (4:Fin 5)≠3),
    (g t).extent_ne (by
      change (m 3:ℂ)+m 4≠0
      exact_mod_cast ne_of_gt (add_pos (hm 3) (hm 4)))]
end
end CentralConfigurations.FiveBody.D2.Regular
