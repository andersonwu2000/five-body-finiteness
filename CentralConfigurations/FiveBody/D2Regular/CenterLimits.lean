import CentralConfigurations.FiveBody.D2Regular.ChartLimits
import CentralConfigurations.FiveBody.D2Regular.Energy

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I : ℂ}

theorem selected_triangle_z_long_zero (s : ActualLimit m q l I) (i : Fin 3) :
    Tendsto (fun t => (q (s.subsequence t)).inverseScale*(q (s.subsequence t)).z (tripleIndex i))
      atTop (𝓝 0) := by
  have hh := (s.triangle_z_limit i).mul (s.scale_limit.pow 2)
  simp only [zero_pow (by decide : 2≠0),mul_zero] at hh
  apply hh.congr
  intro t
  field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) (s.subsequence t)]

theorem selected_pair_w_long_zero (s : ActualLimit m q l I) (p : Fin 2) :
    Tendsto (fun t => (q (s.subsequence t)).inverseScale*(q (s.subsequence t)).w (pairIndex p))
      atTop (𝓝 0) := by
  have hh := (s.pair_w_limit p).mul (s.scale_limit.pow 2)
  simp only [zero_pow (by decide : 2≠0),mul_zero] at hh
  apply hh.congr
  intro t
  field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) (s.subsequence t)]

namespace GaugeExtraction
variable {s : ActualLimit m q l I} (e : GaugeExtraction s) (hm : ∀ i, 0<m i)

def zetaValue (p : Fin 2) : ℂ := e.ratio*(e.ratio*s.triangle.w 2)*(-s.pairZ p)
def etaZValue : ℂ :=
  (pairMass (fun i => (m i:ℂ))+tripleMass (fun i => (m i:ℂ)))/
    (pairMass (fun i => (m i:ℂ))*tripleMass (fun i => (m i:ℂ)))*
  (∑ p : Fin 2, ∑ i : Fin 3, (m (pairIndex p):ℂ)*m (tripleIndex i)*
    (s.cross p i/e.ratio)^3*e.zetaValue p)
def etaWValue : ℂ :=
  (pairMass (fun i => (m i:ℂ))+tripleMass (fun i => (m i:ℂ)))/
    (pairMass (fun i => (m i:ℂ))*tripleMass (fun i => (m i:ℂ)))*
  (∑ p : Fin 2, ∑ i : Fin 3, (m (pairIndex p):ℂ)*m (tripleIndex i)*
    (s.cross p i/e.ratio)^3*(s.triangle.w i/s.triangle.w 2))

theorem zeta_limit_raw (p : Fin 2) (i : Fin 3) :
    Tendsto (fun t => (e.chart hm t).zeta p i) atTop (𝓝 (e.zetaValue p)) := by
  have hp : Tendsto (fun t => (q (s.subsequence t)).inverseScale*(q (s.subsequence t)).z (pairIndex p))
      atTop (𝓝 (s.pairZ p)) := by
    rw [s.pairZ_eq]
    exact (l.z_position (pairIndex p)).comp s.strictMono.tendsto_atTop
  have hh := (e.ratio_limit.mul e.rotation_limit).mul
    (((selected_triangle_z_long_zero s i).sub hp).comp e.strictMono.tendsto_atTop)
  simp only [zero_sub] at hh
  apply hh.congr
  intro t
  rw [(e.chart hm t).zeta_eq]
  dsimp [chart,ReciprocalGauge.chart,ReciprocalGauge.normalized,ZWSystem.rescale]
  field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) (s.subsequence (e.select t))]

theorem chi_limit (p : Fin 2) (i : Fin 3) :
    Tendsto (fun t => (e.chart hm t).chi p i) atTop (𝓝 (s.triangle.w i/s.triangle.w 2)) := by
  have hi : Tendsto (fun t => (q (s.subsequence t)).inverseScale*(q (s.subsequence t)).w (tripleIndex i))
      atTop (𝓝 (s.triangle.w i)) := by
    rw [s.triangle_w_eq]
    exact (l.w_position (tripleIndex i)).comp s.strictMono.tendsto_atTop
  have hh := (e.ratio_limit.mul
    ((hi.sub (selected_pair_w_long_zero s p)).comp e.strictMono.tendsto_atTop)).div
    e.rotation_limit e.rotation_limit_ne
  simp only [sub_zero] at hh
  have hc : e.ratio*s.triangle.w i/(e.ratio*s.triangle.w 2)=s.triangle.w i/s.triangle.w 2 := by
    field_simp [e.ratio_ne,s.w_ne_zero 2]
  rw [hc] at hh
  apply hh.congr
  intro t
  rw [(e.chart hm t).chi_eq]
  dsimp [chart,ReciprocalGauge.chart,ReciprocalGauge.normalized,ZWSystem.rescale]
  field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) (s.subsequence (e.select t))]

theorem etaZ_limit : Tendsto (fun t => (e.chart hm t).etaZ) atTop (𝓝 e.etaZValue) := by
  have hh := (tendsto_finsetSum Finset.univ (fun p _ => tendsto_finsetSum Finset.univ (fun i _ =>
    (((e.cross_limit hm p i).pow 3).const_mul ((m (pairIndex p):ℂ)*m (tripleIndex i))).mul
      (e.zeta_limit_raw hm p i)))).const_mul
        ((pairMass (fun i => (m i:ℂ))+tripleMass (fun i => (m i:ℂ)))/
          (pairMass (fun i => (m i:ℂ))*tripleMass (fun i => (m i:ℂ))))
  exact hh.congr (fun t => (e.chart hm t).etaZ_equation.symm)

theorem etaW_limit : Tendsto (fun t => (e.chart hm t).etaW) atTop (𝓝 e.etaWValue) := by
  have hh := (tendsto_finsetSum Finset.univ (fun p _ => tendsto_finsetSum Finset.univ (fun i _ =>
    (((e.cross_limit hm p i).pow 3).const_mul ((m (pairIndex p):ℂ)*m (tripleIndex i))).mul
      (e.chi_limit hm p i)))).const_mul
        ((pairMass (fun i => (m i:ℂ))+tripleMass (fun i => (m i:ℂ)))/
          (pairMass (fun i => (m i:ℂ))*tripleMass (fun i => (m i:ℂ))))
  exact hh.congr (fun t => (e.chart hm t).etaW_equation.symm)

theorem zeta_limit (p : Fin 2) (i : Fin 3) :
    Tendsto (fun t => (e.chart hm t).zeta p i) atTop (𝓝 (-(![-(m 4:ℂ),(m 3:ℂ)] p))) := by
  have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => -(![-(m 4:ℂ),(m 3:ℂ)] p)) atTop (𝓝 _)).add
    ((e.time_zero.pow 2).mul (e.c_limit hm i))).add ((e.time_zero.pow 3).mul (e.etaZ_limit hm))
  simp only [zero_pow (by decide : 2≠0),zero_pow (by decide : 3≠0),zero_mul,add_zero] at hh
  exact hh

theorem full_centroid_remainder_zero : Tendsto
    (fun t => (e.chart hm t).time^4*(e.chart hm t).etaZ*(e.chart hm t).etaW)
    atTop (𝓝 0) := by
  have hh := ((e.time_zero.pow 4).mul (e.etaZ_limit hm)).mul (e.etaW_limit hm)
  simpa only [zero_pow (by decide : 4≠0),zero_mul] using hh

end GaugeExtraction
end
end CentralConfigurations.FiveBody.D2.Regular
