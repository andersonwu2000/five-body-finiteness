import CentralConfigurations.FiveBody.D2Regular.TorqueDerivative
import CentralConfigurations.FiveBody.D2Regular.InverseActual
import CentralConfigurations.FiveBody.D2Regular.ResponseContradiction

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter
open scoped Topology BigOperators
set_option maxHeartbeats 3000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

include hm in
theorem leadingE_norm_ne : bilinear (shapeMass m) (leadingE s) (leadingE s)≠0 := by
  have hn : ∀ i : Fin 3, shapeMass m i≠0 :=
    fun i => Complex.ofReal_ne_zero.mpr (ne_of_gt (hm (tripleIndex i)))
  have hB : shapeMass m 0+shapeMass m 1+shapeMass m 2≠0 := by
    change (m 0:ℂ)+m 1+m 2≠0
    exact_mod_cast ne_of_gt (add_pos (add_pos (hm 0) (hm 1)) (hm 2))
  dsimp only [leadingE]
  rw [transverse_norm (shapeMass m) (leadingD s) hn (normalizedTriangle s).mass_center_w]
  exact div_ne_zero (mul_ne_zero hB (normalized_nonisotropic s))
    (mul_ne_zero (mul_ne_zero (hn 0) (hn 1)) (hn 2))

include hm in
/-- Local-inverse consumer. Its Jacobian and two row identities are supplied
by the separately proved explicit finite residual derivative. -/
theorem false_of_regular_jacobian
    (hell : transverseEigenvalue s.triangle≠0)
    (J : ChartSpace ≃L[ℂ] ChartSpace)
    (hJ : HasStrictFDerivAt (augmentedResidual s e) (J : ChartSpace →L[ℂ] ChartSpace)
      (0,baseCoordinates s e))
    (hZ : ∀ v : ChartSpace, (J v).2 2=
      bilinear (shapeMass m) (leadingE s) (leadingE s)*
        ((1+transverseEigenvalue s.triangle/2)*v.2 2+
          (3*normalizedKappa s*transverseEigenvalue s.triangle/2)*v.2 3)-v.1*torqueResponse s e)
    (hW : ∀ v : ChartSpace, (J v).2 3=
      bilinear (shapeMass m) (leadingE s) (leadingE s)*
        ((3*transverseEigenvalue s.triangle/(2*normalizedKappa s))*v.2 2+
          (1+transverseEigenvalue s.triangle/2)*v.2 3)) : False := by
  let v := J.symm ((1:ℂ),(0:Fin 6 → ℂ))
  have hJv : J v=((1:ℂ),(0:Fin 6 → ℂ)) := J.apply_symm_apply _
  have htime : Tendsto (fun t => (e.chart hm t).time) atTop (𝓝 0) := e.time_zero
  have hbase : augmentedResidual s e (0,baseCoordinates s e)=(0,0) := by
    dsimp [augmentedResidual]
    rw [finiteResidual_base s e hm]
  have hres : ∀ᶠ t in atTop,
      augmentedResidual s e ((e.chart hm t).time,actualCoordinates s e hm t)=((e.chart hm t).time,0) := by
    filter_upwards [finiteResidual_actual s e hm] with t ht
    dsimp [augmentedResidual]
    rw [ht]
  have ht := actual_inverse_torque_derivative_zero J hJ hbase
    (htime.prodMk_nhds (actual_coordinates_limit s e hm)) htime (fun t => (e.chart hm t).time_ne)
    hres ((-torqueResponse s e/2) • chartCoord 3) (modelTorque_strictFDerivAt s e hm)
    (modelTorque_base s e hm) (modelTorque_actual_div_time_zero s e hm)
  change (-torqueResponse s e/2)*v.2 3=0 at ht
  have hz := hZ v
  have hw := hW v
  rw [hJv] at hz hw
  have hv1 : v.1=1 := by
    have hh := congrArg Prod.fst hJv
    -- The time row of the actual augmented derivative is the identity.
    have hfst := hJ.hasFDerivAt.fst
    have hid : HasFDerivAt (fun x : ChartSpace => x.1) hCoord (0,baseCoordinates s e) := hCoord.hasFDerivAt
    have he := hfst.unique hid
    have hev := congrArg (fun D : ChartSpace →L[ℂ] ℂ => D v) he
    change (J v).1=v.1 at hev
    rw [hJv] at hev
    exact hev.symm
  have hz' : bilinear (shapeMass m) (leadingE s) (leadingE s)*
      ((1+transverseEigenvalue s.triangle/2)*v.2 2+
        (3*normalizedKappa s*transverseEigenvalue s.triangle/2)*v.2 3)=torqueResponse s e := by
    simp only [hv1,one_mul,Pi.zero_apply] at hz
    exact sub_eq_zero.mp hz.symm
  exact false_of_response_and_torque (normalized_kappa_ne s) hell (leadingE_norm_ne s hm)
    (torqueResponse_ne s e hm) hz' hw.symm ht

end
end CentralConfigurations.FiveBody.D2.Regular



