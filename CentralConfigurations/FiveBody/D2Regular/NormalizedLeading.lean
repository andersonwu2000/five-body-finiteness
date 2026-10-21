import CentralConfigurations.FiveBody.D2Regular.CenterLimits
import CentralConfigurations.FiveBody.D2Regular.PairForces
import CentralConfigurations.FiveBody.D2Regular.PlaneCoordinates

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}

def normalizedTriangle (s : PhysicalEulerLimit m q l I0) :=
  s.triangle.rescale (s.triangle.w 2) (s.w_ne_zero 2)

def normalizedKappa (s : PhysicalEulerLimit m q l I0) : ℂ :=
  s.signedEuler.theta^2*s.triangle.w 2^2

theorem normalized_last (s : PhysicalEulerLimit m q l I0) : (normalizedTriangle s).w 2=1 := by
  dsimp [normalizedTriangle,ZWSystem.rescale]
  field_simp [s.w_ne_zero 2]

theorem normalized_kappa_ne (s : PhysicalEulerLimit m q l I0) : normalizedKappa s≠0 :=
  mul_ne_zero (pow_ne_zero 2 s.signedEuler.theta_ne_zero) (pow_ne_zero 2 (s.w_ne_zero 2))

theorem normalized_proportional (s : PhysicalEulerLimit m q l I0) (i : Fin 3) :
    (normalizedTriangle s).z i=normalizedKappa s*(normalizedTriangle s).w i := by
  dsimp [normalizedTriangle,normalizedKappa,ZWSystem.rescale]
  rw [s.signedEuler.proportional i]
  field_simp [s.w_ne_zero 2]

theorem normalized_nonisotropic (s : PhysicalEulerLimit m q l I0) :
    bilinear (fun i : Fin 3 => (m (tripleIndex i):ℂ))
      (normalizedTriangle s).w (normalizedTriangle s).w≠0 := by
  have he : bilinear (fun i : Fin 3 => (m (tripleIndex i):ℂ))
      (normalizedTriangle s).w (normalizedTriangle s).w=
      (∑ i : Fin 3, (m (tripleIndex i):ℂ)*s.triangle.w i^2)/s.triangle.w 2^2 := by
    dsimp [bilinear,normalizedTriangle,ZWSystem.rescale]
    simp [Fin.sum_univ_succ]
    ring
  rw [he]
  exact div_ne_zero s.nonisotropic (pow_ne_zero 2 (s.w_ne_zero 2))

theorem normalized_ell (s : PhysicalEulerLimit m q l I0) :
    transverseEigenvalue (normalizedTriangle s)=transverseEigenvalue s.triangle := rfl

namespace GaugeExtraction
variable {s : ActualLimit m q l (I0:ℂ)} (e : GaugeExtraction s) (hm : ∀ i, 0<m i)

def betaValue : ℂ := (s.pairW 1-s.pairW 0)/
  (pairMass (fun i => (m i:ℂ))*(e.ratio*s.triangle.w 2)*e.ratio)

include hm

theorem pair_leading_metric : s.pairDelta^2*pairMass (fun i => (m i:ℂ))^2*e.betaValue=1 := by
  have hh := (((e.pair_delta_limit hm).pow 2).mul_const (pairMass (fun i => (m i:ℂ))^2)).mul
    (e.beta_limit hm)
  apply tendsto_nhds_unique hh
  have he (t : ℕ) : (e.chart hm t).point.delta 3 4^2*
      pairMass (fun i => (m i:ℂ))^2*(e.chart hm t).beta=1 := (e.chart hm t).pair_metric
  simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1))

theorem betaValue_ne : e.betaValue≠0 := by
  intro hh
  have he := e.pair_leading_metric hm
  rw [hh,mul_zero] at he
  exact zero_ne_one he

theorem cross_leading_metric (p : Fin 2) (i : Fin 3) :
    (s.cross p i/e.ratio)^2*(-(![-(m 4:ℂ),(m 3:ℂ)] p))*(s.triangle.w i/s.triangle.w 2)=1 := by
  have hh := (((e.cross_limit hm p i).pow 2).mul (e.zeta_limit hm p i)).mul (e.chi_limit hm p i)
  apply tendsto_nhds_unique hh
  have he (t : ℕ) : (e.chart hm t).cross p i^2*(e.chart hm t).zeta p i*(e.chart hm t).chi p i=1 :=
    (e.chart hm t).cross_metric p i
  simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1))

end GaugeExtraction
end
end CentralConfigurations.FiveBody.D2.Regular
