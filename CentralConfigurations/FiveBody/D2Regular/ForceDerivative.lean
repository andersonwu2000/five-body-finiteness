import CentralConfigurations.FiveBody.D2Regular.RootSheet
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped Topology

/-- Differentiation of a force through its original local root sheet. This
gives the two coefficients used by the Euler shape Jacobian. -/
theorem force_strictFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c d : E → ℂ} {c' d' : E →L[ℂ] ℂ} {x : E} {k w r : ℂ}
    (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x)
    (hcv : c x=k*w) (hdv : d x=w) (hk : k≠0) (hw : w≠0) :
    HasStrictFDerivAt (fun y => rootSheet r (k*w^2) (c y*d y)^3*c y)
      ((-r^3/2) • c'-(3*k*r^3/2) • d') x := by
  have hP : k*w^2≠0 := mul_ne_zero hk (pow_ne_zero 2 hw)
  have hp := hc.mul hd
  have he : k*w^2=c x*d x := by rw [hcv,hdv]; ring
  have hr := (rootSheet_strictDeriv (r0 := r) hP).comp_hasStrictFDerivAt_of_eq x hp he
  have hf := (hr.pow 3).mul hc
  convert hf using 1
  ext y
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,smul_eq_mul,Function.comp_apply,Pi.mul_apply,hcv,hdv,
    show k*w*w=k*w^2 by ring,rootSheet_self hP]
  field_simp [hk,hw]
  ring

end
end CentralConfigurations.FiveBody.D2.Regular
