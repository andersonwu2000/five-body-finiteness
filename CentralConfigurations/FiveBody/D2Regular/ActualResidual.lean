import CentralConfigurations.FiveBody.D2Regular.ActualSheets
import CentralConfigurations.FiveBody.D2Regular.TorqueLimit

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter
open scoped Topology BigOperators
set_option maxHeartbeats 3000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

theorem finiteResidual_actual_of_sheets (t : ℕ)
    (hp : (e.chart hm t).point.delta 3 4=modelPairRoot s e (actualCoordinates s e hm t))
    (htri : ∀ i j, (e.chart hm t).point.delta (tripleIndex i) (tripleIndex j)=
      modelTriangleRoot s (actualCoordinates s e hm t) i j)
    (hcross : ∀ p i, (e.chart hm t).cross p i=
      modelCrossRoot s e (e.chart hm t).time (actualCoordinates s e hm t) p i) :
    finiteResidual s e (e.chart hm t).time (actualCoordinates s e hm t)=0 := by
  have hHz (i : Fin 3) : modelHz s e (e.chart hm t).time (actualCoordinates s e hm t) i=(e.chart hm t).Hz i := by
    dsimp [modelHz,ActualChart.Hz]
    simp_rw [← hcross,actual_modelZeta]
  have hHw (i : Fin 3) : modelHw s e (e.chart hm t).time (actualCoordinates s e hm t) i=(e.chart hm t).Hw i := by
    dsimp [modelHw,ActualChart.Hw]
    simp_rw [← hcross,actual_modelChi]
  have hGz (p : Fin 2) : modelGz s e (e.chart hm t).time (actualCoordinates s e hm t) p=(e.chart hm t).Gz p := by
    dsimp [modelGz,ActualChart.Gz]
    simp_rw [← hcross,actual_modelZeta]
  have hFz (i : Fin 3) : modelFz s (actualCoordinates s e hm t) i=(e.chart hm t).Fz i := by
    dsimp [modelFz,ActualChart.Fz]
    simp_rw [actual_modelC,← htri]
  have hFw (i : Fin 3) : modelFw s (actualCoordinates s e hm t) i=(e.chart hm t).Fw i := by
    dsimp [modelFw,ActualChart.Fw]
    simp_rw [actual_modelD,← htri]
  have hZ (i : Fin 3) : modelTripleResidualZ s e (e.chart hm t).time (actualCoordinates s e hm t) i=0 := by
    dsimp [modelTripleResidualZ]
    rw [hFz,funext hHz]
    exact sub_eq_zero.mpr ((e.chart hm t).triangle_z_residual i)
  have hW (i : Fin 3) : modelTripleResidualW s e (e.chart hm t).time (actualCoordinates s e hm t) i=0 := by
    dsimp [modelTripleResidualW]
    rw [hFw,funext hHw]
    exact sub_eq_zero.mpr ((e.chart hm t).triangle_w_residual i)
  have hSZ : modelCrossSumZ s e (e.chart hm t).time (actualCoordinates s e hm t)=(e.chart hm t).crossSumZ := by
    dsimp [modelCrossSumZ,ActualChart.crossSumZ]
    simp_rw [← hcross,actual_modelZeta]
  have hSW : modelCrossSumW s e (e.chart hm t).time (actualCoordinates s e hm t)=(e.chart hm t).crossSumW := by
    dsimp [modelCrossSumW,ActualChart.crossSumW]
    simp_rw [← hcross,actual_modelChi]
  funext i
  fin_cases i
  · change (1-pairMass (fun j => (m j:ℂ))*modelPairRoot s e (actualCoordinates s e hm t)^3)+
      (e.chart hm t).time^3*(modelGz s e (e.chart hm t).time (actualCoordinates s e hm t) 0-
        (∑ p : Fin 2, (m (pairIndex p):ℂ)*modelGz s e (e.chart hm t).time (actualCoordinates s e hm t) p)/
          pairMass (fun j => (m j:ℂ)))/modelA (m := m) 0=0
    simp_rw [← hp,hGz]
    have hh := (e.chart hm t).pair_z_residual 0
    have ha : modelA (m := m) 0≠0 := neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt (hm 4)))
    dsimp [modelA,ActualChart.a,ActualChart.meanP] at ha hh ⊢
    have hm4 : (m 4:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm 4))
    field_simp [hm4,(e.chart hm t).pairMass_ne] at hh ⊢
    linear_combination -hh
  · change bilinear (shapeMass m) (leadingD s) (modelTripleResidualW s e (e.chart hm t).time (actualCoordinates s e hm t))=0
    simp only [bilinear,hW,mul_zero,Finset.sum_const_zero]
  · change bilinear (shapeMass m) (leadingE s) (modelTripleResidualZ s e (e.chart hm t).time (actualCoordinates s e hm t))=0
    simp only [bilinear,hZ,mul_zero,Finset.sum_const_zero]
  · change bilinear (shapeMass m) (leadingE s) (modelTripleResidualW s e (e.chart hm t).time (actualCoordinates s e hm t))=0
    simp only [bilinear,hW,mul_zero,Finset.sum_const_zero]
  · change (e.chart hm t).etaZ-_=0
    rw [hSZ]
    exact sub_eq_zero.mpr (e.chart hm t).etaZ_equation
  · change (e.chart hm t).etaW-_=0
    rw [hSW]
    exact sub_eq_zero.mpr (e.chart hm t).etaW_equation

theorem finiteResidual_actual : ∀ᶠ t in atTop,
    finiteResidual s e (e.chart hm t).time (actualCoordinates s e hm t)=0 := by
  filter_upwards [all_actual_sheets s e hm] with t ht
  exact finiteResidual_actual_of_sheets s e hm t ht.1 ht.2.1 ht.2.2

theorem modelTorque_actual : ∀ᶠ t in atTop,
    modelUnsquaredTorque s e (e.chart hm t).time (actualCoordinates s e hm t)=(e.chart hm t).unsquaredTorque := by
  filter_upwards [all_actual_sheets s e hm] with t ht
  dsimp [modelUnsquaredTorque,ActualChart.unsquaredTorque]
  simp_rw [← ht.2.2]

theorem modelTorque_actual_div_time_zero : Tendsto
    (fun t => modelUnsquaredTorque s e (e.chart hm t).time (actualCoordinates s e hm t)/(e.chart hm t).time)
    atTop (𝓝 0) := by
  apply (e.unsquared_torque_div_time_zero hm).congr'
  filter_upwards [modelTorque_actual s e hm] with t ht
  rw [ht]

end
end CentralConfigurations.FiveBody.D2.Regular


