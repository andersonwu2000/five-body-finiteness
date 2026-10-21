import CentralConfigurations.FiveBody.D2Regular.TorqueResponse
import CentralConfigurations.FiveBody.D2Jacobian.CrossDerivative

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

include hm in
theorem modelTorque_base : modelUnsquaredTorque s e 0 (baseCoordinates s e)=0 := by
  dsimp [modelUnsquaredTorque]
  simp_rw [modelCrossRoot_base s e hm]
  rw [Finset.sum_comm]
  have he (i : Fin 3) :
      (∑ p : Fin 2, (m (pairIndex p):ℂ)*shapeMass m i*(s.cross p i/e.ratio))=
      shapeMass m i*leadingB s e i := by
    simp [Fin.sum_univ_succ,leadingB,pairIndex]
    ring
  simp_rw [he]
  exact leadingB_centered s e

include hm in
theorem modelTorque_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => modelUnsquaredTorque s e v.1 v.2)
      ((-torqueResponse s e/2) • chartCoord 3) (0,baseCoordinates s e) := by
  have hh := HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun p _ =>
    HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (crossRoot_strictFDerivAt s e hm p i).const_mul ((m (pairIndex p):ℂ)*shapeMass m i)))
  apply hh.congr_fderiv
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
    dDerivative,chartCoord_apply]
  rw [Finset.sum_comm,← torque_slope_eq s e hm]
  simp only [neg_div,Finset.sum_div]
  rw [← Finset.sum_neg_distrib,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Fin.sum_univ_two]
  dsimp [leadingB,pairIndex]
  field_simp [leadingD_ne s i]
  ring

end
end CentralConfigurations.FiveBody.D2.Regular



