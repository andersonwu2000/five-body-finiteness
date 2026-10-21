import CentralConfigurations.FiveBody.D2Regular.NormalizedLeading
import CentralConfigurations.FiveBody.D2Regular.Torque

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
namespace GaugeExtraction
variable {s : ActualLimit m q l (I0:ℂ)} (e : GaugeExtraction s) (hm : ∀ i, 0<m i)

def torqueRemainderValue : ℂ := ∑ p : Fin 2, ∑ i : Fin 3,
  (m (pairIndex p):ℂ)*m (tripleIndex i)*(s.cross p i/e.ratio)^3*
    ((s.triangle.w 2*s.triangle.z i)*(s.triangle.w i/s.triangle.w 2)-
      e.betaValue*(![-(m 4:ℂ),(m 3:ℂ)] p)*e.zetaValue p)

def crossSumWValue : ℂ := ∑ p : Fin 2, ∑ i : Fin 3,
  (m (pairIndex p):ℂ)*m (tripleIndex i)*(s.cross p i/e.ratio)^3*(s.triangle.w i/s.triangle.w 2)

theorem torqueRemainder_limit :
    Tendsto (fun t => (e.chart hm t).torqueRemainder) atTop (𝓝 e.torqueRemainderValue) := by
  apply tendsto_finsetSum Finset.univ
  intro p _
  apply tendsto_finsetSum Finset.univ
  intro i _
  exact (((e.cross_limit hm p i).pow 3).const_mul ((m (pairIndex p):ℂ)*m (tripleIndex i))).mul
    (((e.c_limit hm i).mul (e.chi_limit hm p i)).sub
      (((e.beta_limit hm).mul_const (![-(m 4:ℂ),(m 3:ℂ)] p)).mul (e.zeta_limit_raw hm p i)))

theorem crossSumW_limit :
    Tendsto (fun t => (e.chart hm t).crossSumW) atTop (𝓝 e.crossSumWValue) := by
  apply tendsto_finsetSum Finset.univ
  intro p _
  apply tendsto_finsetSum Finset.univ
  intro i _
  exact (((e.cross_limit hm p i).pow 3).const_mul ((m (pairIndex p):ℂ)*m (tripleIndex i))).mul
    (e.chi_limit hm p i)

/-- The original remaining torque has zero first coefficient on every actual
selected sequence. No correction rate or analytic curve is assumed here. -/
theorem unsquared_torque_div_time_zero :
    Tendsto (fun t => (e.chart hm t).unsquaredTorque/(e.chart hm t).time) atTop (𝓝 0) := by
  have hh := (e.time_zero.mul (e.torqueRemainder_limit hm)).add
    (((e.time_zero.pow 2).mul (e.etaZ_limit hm)).mul (e.crossSumW_limit hm))
  simp only [zero_mul,zero_pow (by decide : 2≠0),zero_add] at hh
  apply hh.congr
  intro t
  change (e.chart hm t).time*(e.chart hm t).torqueRemainder+
    (e.chart hm t).time^2*(e.chart hm t).etaZ*(e.chart hm t).crossSumW=
      (e.chart hm t).unsquaredTorque/(e.chart hm t).time
  field_simp [(e.chart hm t).time_ne]
  linear_combination -(e.chart hm t).unsquared_torque_equation

end GaugeExtraction
end
end CentralConfigurations.FiveBody.D2.Regular
