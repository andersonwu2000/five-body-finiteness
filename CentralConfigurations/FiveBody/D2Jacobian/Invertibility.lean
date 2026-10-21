import CentralConfigurations.FiveBody.D2Jacobian.ResidualDerivative

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

@[simp] theorem augmentedJacobian_first (v : ChartSpace) : (augmentedJacobian s e v).1=v.1 := rfl
@[simp] theorem augmentedJacobian_row (v : ChartSpace) (i : Fin 6) :
    (augmentedJacobian s e v).2 i=residualRows s e i v := rfl

theorem augmentedJacobian_row_zero (v : ChartSpace) :
    (augmentedJacobian s e v).2 0=3*v.2 0/(2*e.betaValue) := by
  change pairRow s e v=_
  simp only [pairRow,
    ContinuousLinearMap.smul_apply,smul_eq_mul,chartCoord_apply]; ring

theorem augmentedJacobian_row_one (v : ChartSpace) :
    (augmentedJacobian s e v).2 1=shapeNorm s*
      (3*v.2 1/(2*normalizedKappa s)-3*leadingE s 2*v.2 3/2) := by
  change longitudinalRow s v=_
  simp only [longitudinalRow,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,smul_eq_mul,chartCoord_apply]; ring

theorem augmentedJacobian_row_two (v : ChartSpace) :
    (augmentedJacobian s e v).2 2=transverseNorm s*
      ((1+transverseEigenvalue s.triangle/2)*v.2 2+
        (3*normalizedKappa s*transverseEigenvalue s.triangle/2)*v.2 3)-
      v.1*bilinear (shapeMass m) (leadingE s) (jacobianResponse s e) := by
  change transverseZRow s e v=_
  simp only [transverseZRow,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.add_apply,smul_eq_mul,chartCoord_apply,hCoord_apply]; ring

theorem augmentedJacobian_row_three (v : ChartSpace) :
    (augmentedJacobian s e v).2 3=transverseNorm s*
      ((3*transverseEigenvalue s.triangle/(2*normalizedKappa s))*v.2 2+
        (1+transverseEigenvalue s.triangle/2)*v.2 3) := by
  change transverseWRow s v=_
  simp only [transverseWRow,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    smul_eq_mul,chartCoord_apply]

include hm in
theorem augmentedJacobian_kernel (hhalf : transverseEigenvalue s.triangle≠ -(1/2:ℂ))
    {v : ChartSpace} (hv : augmentedJacobian s e v=0) : v=0 := by
  have ht : v.1=0 := by simpa only [augmentedJacobian_first] using congrArg Prod.fst hv
  have hh (i : Fin 6) : (augmentedJacobian s e v).2 i=0 := by
    simpa using congrArg (fun w : ChartSpace => w.2 i) hv
  have hbeta : v.2 0=0 := by
    have hh0 := hh 0
    rw [augmentedJacobian_row_zero] at hh0
    field_simp [e.betaValue_ne hm] at hh0
    linear_combination hh0/3
  have hrows := selected_shape_rows_injective (k := normalizedKappa s)
    (ell := transverseEigenvalue s.triangle) (S := shapeNorm s) (N := transverseNorm s)
    (e2 := leadingE s 2) (d2 := 1) (u := v.2 1) (v := v.2 2) (y := v.2 3)
    (normalized_kappa_ne s) s.transverse_ne_one hhalf (shapeNorm_ne s) (transverseNorm_ne s hm)
    (by simpa only [augmentedJacobian_row_one,mul_one] using hh 1)
    (by simpa only [augmentedJacobian_row_two,ht,zero_mul,sub_zero] using hh 2)
    (by simpa only [augmentedJacobian_row_three] using hh 3)
  rcases hrows with ⟨hu,hv',hy⟩
  have hZ : v.2 4=0 := by
    simpa [residualRows,centerZRow,crossSumZDerivative,dDerivative,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,smul_eq_mul,hy] using hh 4
  have hW : v.2 5=0 := by
    simpa [residualRows,centerWRow,crossSumWDerivative,dDerivative,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,smul_eq_mul,hy] using hh 5
  apply Prod.ext ht
  funext i
  fin_cases i <;> assumption

include hm in
theorem augmentedJacobian_injective (hhalf : transverseEigenvalue s.triangle≠ -(1/2:ℂ)) :
    Function.Injective (augmentedJacobian s e) := by
  intro v w hvw
  have hh : augmentedJacobian s e (v-w)=0 := by rw [map_sub,hvw,sub_self]
  exact sub_eq_zero.mp (augmentedJacobian_kernel s e hm hhalf hh)

def regularJacobian (hhalf : transverseEigenvalue s.triangle≠ -(1/2:ℂ)) :
    ChartSpace ≃L[ℂ] ChartSpace :=
  ((augmentedJacobian s e).toLinearMap.linearEquivOfInjective
    (augmentedJacobian_injective s e hm hhalf) rfl).toContinuousLinearEquiv

theorem regularJacobian_eq (hhalf : transverseEigenvalue s.triangle≠ -(1/2:ℂ)) :
    (regularJacobian s e hm hhalf : ChartSpace →L[ℂ] ChartSpace)=augmentedJacobian s e := by
  apply ContinuousLinearMap.ext; intro v; rfl

theorem regularJacobian_strictFDerivAt (hhalf : transverseEigenvalue s.triangle≠ -(1/2:ℂ)) :
    HasStrictFDerivAt (augmentedResidual s e)
      (regularJacobian s e hm hhalf : ChartSpace →L[ℂ] ChartSpace) (0,baseCoordinates s e) := by
  rw [regularJacobian_eq]
  exact augmented_strictFDerivAt s e hm

include hm in
/-- The actual retained Euler-limit chart has an invertible strict derivative.
No row-rank, Jacobian, or sheet-selection premise is used. -/
theorem exists_regularJacobian (hhalf : transverseEigenvalue s.triangle≠ -(1/2:ℂ)) :
    ∃ J : ChartSpace ≃L[ℂ] ChartSpace,
      HasStrictFDerivAt (augmentedResidual s e) (J : ChartSpace →L[ℂ] ChartSpace)
        (0,baseCoordinates s e) :=
  ⟨regularJacobian s e hm hhalf,regularJacobian_strictFDerivAt s e hm hhalf⟩

include hm in
/-- First-order selected rows for any response to the time direction. -/
theorem regularJacobian_response_rows (hhalf : transverseEigenvalue s.triangle≠ -(1/2:ℂ))
    {v : ChartSpace} (hv : regularJacobian s e hm hhalf v=(v.1,0)) :
    v.2 0=0 ∧
    shapeNorm s*(3*v.2 1/(2*normalizedKappa s)-3*leadingE s 2*v.2 3/2)=0 ∧
    transverseNorm s*((1+transverseEigenvalue s.triangle/2)*v.2 2+
      (3*normalizedKappa s*transverseEigenvalue s.triangle/2)*v.2 3)=
        v.1*bilinear (shapeMass m) (leadingE s) (jacobianResponse s e) ∧
    transverseNorm s*((3*transverseEigenvalue s.triangle/(2*normalizedKappa s))*v.2 2+
      (1+transverseEigenvalue s.triangle/2)*v.2 3)=0 := by
  have hh (i : Fin 6) : (augmentedJacobian s e v).2 i=0 := by
    have he := congrArg (fun w : ChartSpace => w.2 i) hv
    simpa only [← regularJacobian_eq s e hm hhalf] using he
  have hbeta : v.2 0=0 := by
    have hh0 := hh 0
    rw [augmentedJacobian_row_zero] at hh0
    field_simp [e.betaValue_ne hm] at hh0
    linear_combination hh0/3
  exact ⟨hbeta,by simpa only [augmentedJacobian_row_one] using hh 1,
    sub_eq_zero.mp (by simpa only [augmentedJacobian_row_two] using hh 2),
    by simpa only [augmentedJacobian_row_three] using hh 3⟩

end
end CentralConfigurations.FiveBody.D2.Regular
