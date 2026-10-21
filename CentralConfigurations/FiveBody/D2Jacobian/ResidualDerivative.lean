import CentralConfigurations.FiveBody.D2Jacobian.SelectedRows

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

def pairRow : ChartSpace →L[ℂ] ℂ := (3/(2*e.betaValue)) • chartCoord 0
def centerZRow : ChartSpace →L[ℂ] ℂ := chartCoord 4-
  ((pairMass (fun i => (m i:ℂ))+tripleMass (fun i => (m i:ℂ)))/
    (pairMass (fun i => (m i:ℂ))*tripleMass (fun i => (m i:ℂ)))) • crossSumZDerivative s e
def centerWRow : ChartSpace →L[ℂ] ℂ := chartCoord 5-
  ((pairMass (fun i => (m i:ℂ))+tripleMass (fun i => (m i:ℂ)))/
    (pairMass (fun i => (m i:ℂ))*tripleMass (fun i => (m i:ℂ)))) • crossSumWDerivative s e
def residualRows : Fin 6 → ChartSpace →L[ℂ] ℂ :=
  ![pairRow s e,longitudinalRow s,transverseZRow s e,transverseWRow s,centerZRow s e,centerWRow s e]
def residualJacobian : ChartSpace →L[ℂ] (Fin 6 → ℂ) := ContinuousLinearMap.pi (residualRows s e)
def augmentedJacobian : ChartSpace →L[ℂ] ChartSpace := hCoord.prod (residualJacobian s e)

include hm

theorem modelPairRoot_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => modelPairRoot s e v.2)
      ((-s.pairDelta/(2*e.betaValue)) • chartCoord 0) (0,baseCoordinates s e) := by
  have hP := pair_base_product_ne s e hm
  have hA : pairMass (fun i => (m i:ℂ))≠0 := by
    intro hh; apply hP; rw [hh,zero_pow (by decide : 2≠0),zero_mul]
  have hp := ((chartCoord 0).hasStrictFDerivAt (x := (0,baseCoordinates s e))).const_mul
    (pairMass (fun i => (m i:ℂ))^2)
  have hr := (rootSheet_strictDeriv (r0 := s.pairDelta) hP).comp_hasStrictFDerivAt_of_eq (0,baseCoordinates s e) hp (by rfl)
  exact hr.congr_fderiv (by
    apply ContinuousLinearMap.ext; intro v
    simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,chartCoord_apply]
    field_simp [hA,e.betaValue_ne hm])

theorem pairResidual_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => (finiteResidual s e v.1 v.2) 0)
      (pairRow s e) (0,baseCoordinates s e) := by
  have hp := (((modelPairRoot_strictFDerivAt s e hm).pow 3).const_mul (pairMass (fun i => (m i:ℂ)))).const_sub 1
  have hg := ((modelGz_strictFDerivAt s e hm 0).sub (scalar_div_strictFDerivAt (HasStrictFDerivAt.fun_sum
    (u := Finset.univ) (fun p _ => (modelGz_strictFDerivAt s e hm p).const_mul (m (pairIndex p):ℂ))) (pairMass (fun i => (m i:ℂ)))))
  have hh := hp.add (scalar_div_strictFDerivAt ((h_cubed_strictFDerivAt s e).mul hg) (modelA (m := m) 0))
  have hA : pairMass (fun i => (m i:ℂ))≠0 := by
    intro hz
    have he := pair_base_product_ne s e hm
    apply he; rw [hz,zero_pow (by decide : 2≠0),zero_mul]
  have hpair : pairMass (fun i => (m i:ℂ))*s.pairDelta^3=1 := by
    change ((m 3:ℂ)+m 4)*s.pairDelta^3=1
    change (m 3:ℂ)+m 4≠0 at hA
    rw [s.pair_delta_cube]; field_simp [hA]
  exact hh.congr_fderiv (by
    apply ContinuousLinearMap.ext; intro v
    simp only [pairRow,ContinuousLinearMap.neg_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.add_apply,ContinuousLinearMap.zero_apply,smul_eq_mul,
      chartCoord_apply,modelPairRoot_base s e hm,nsmul_eq_mul]
    simp only [zero_pow (by decide : 3≠0),zero_mul,mul_zero,add_zero]
    field_simp [e.betaValue_ne hm]
    linear_combination 3*v.2 0*hpair)

theorem tripleZ_strictFDerivAt (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelTripleResidualZ s e v.1 v.2 i)
      (shapeZDerivative s i-jacobianResponse s e i • hCoord) (0,baseCoordinates s e) := by
  have hh := (modelFz_strictFDerivAt s e hm i).sub
    (hCoord.hasStrictFDerivAt.mul (centeredHz_strictFDerivAt s e hm i))
  exact hh.congr_fderiv (by
    have hb : centeredVector (shapeMass m) (modelHz s e 0 (baseCoordinates s e)) i=
        jacobianResponse s e i := by
      simp only [jacobianResponse,centeredVector,weightedCenter]
      simp_rw [modelHz_base s e hm]
    apply ContinuousLinearMap.ext; intro v
    simp [ContinuousLinearMap.smul_apply,smul_eq_mul,hb])

theorem tripleW_strictFDerivAt (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelTripleResidualW s e v.1 v.2 i)
      (shapeWDerivative s i) (0,baseCoordinates s e) := by
  exact ((modelFw_strictFDerivAt s e hm i).sub
    ((h_cubed_strictFDerivAt s e).mul (centeredHw_strictFDerivAt s e hm i))).congr_fderiv (by
      apply ContinuousLinearMap.ext; intro v
      simp [ContinuousLinearMap.smul_apply,smul_eq_mul])

theorem longitudinalResidual_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => (finiteResidual s e v.1 v.2) 1)
      (longitudinalRow s) (0,baseCoordinates s e) := by
  rw [longitudinalRow_eq s hm]
  exact HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (tripleW_strictFDerivAt s e hm i).const_mul (shapeMass m i*leadingD s i))

theorem transverseZResidual_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => (finiteResidual s e v.1 v.2) 2)
      (transverseZRow s e) (0,baseCoordinates s e) := by
  rw [transverseZRow_eq s e hm]
  exact HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (tripleZ_strictFDerivAt s e hm i).const_mul (shapeMass m i*leadingE s i))

theorem transverseWResidual_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => (finiteResidual s e v.1 v.2) 3)
      (transverseWRow s) (0,baseCoordinates s e) := by
  rw [transverseWRow_eq s hm]
  exact HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
    (tripleW_strictFDerivAt s e hm i).const_mul (shapeMass m i*leadingE s i))

theorem centerZResidual_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => (finiteResidual s e v.1 v.2) 4)
      (centerZRow s e) (0,baseCoordinates s e) := by
  exact (chartCoord 4).hasStrictFDerivAt.sub ((modelCrossSumZ_strictFDerivAt s e hm).const_mul _)

theorem centerWResidual_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => (finiteResidual s e v.1 v.2) 5)
      (centerWRow s e) (0,baseCoordinates s e) := by
  exact (chartCoord 5).hasStrictFDerivAt.sub ((modelCrossSumW_strictFDerivAt s e hm).const_mul _)

theorem residual_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => finiteResidual s e v.1 v.2)
      (residualJacobian s e) (0,baseCoordinates s e) := by
  apply hasStrictFDerivAt_pi'.2
  intro i
  fin_cases i
  · exact pairResidual_strictFDerivAt s e hm
  · exact longitudinalResidual_strictFDerivAt s e hm
  · exact transverseZResidual_strictFDerivAt s e hm
  · exact transverseWResidual_strictFDerivAt s e hm
  · exact centerZResidual_strictFDerivAt s e hm
  · exact centerWResidual_strictFDerivAt s e hm

theorem augmented_strictFDerivAt :
    HasStrictFDerivAt (augmentedResidual s e) (augmentedJacobian s e) (0,baseCoordinates s e) :=
  hCoord.hasStrictFDerivAt.prodMk (residual_strictFDerivAt s e hm)

end
end CentralConfigurations.FiveBody.D2.Regular

