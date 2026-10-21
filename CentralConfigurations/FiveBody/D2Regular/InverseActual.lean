import CentralConfigurations.FiveBody.D2Regular.ActualResidual
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- An invertible strict derivative puts every approaching exact residual
zero on the unique local graph. The original sequence need not be analytic. -/
theorem actual_inverse_torque_derivative_zero
    {f : E → ℂ × F} {a : E} (J : E ≃L[ℂ] ℂ × F)
    (hf : HasStrictFDerivAt f (J : E →L[ℂ] ℂ × F) a) (hf0 : f a=(0,0))
    {p : ℕ → E} {h : ℕ → ℂ} (hp : Tendsto p atTop (𝓝 a))
    (hh : Tendsto h atTop (𝓝 0)) (hne : ∀ t, h t≠0)
    (hres : ∀ᶠ t in atTop, f (p t)=(h t,0))
    {W : E → ℂ} (D : E →L[ℂ] ℂ) (hW : HasStrictFDerivAt W D a) (hW0 : W a=0)
    (hWt : Tendsto (fun t => W (p t)/h t) atTop (𝓝 0)) :
    D (J.symm (1,0))=0 := by
  let ins : ℂ →L[ℂ] ℂ × F := ContinuousLinearMap.inl ℂ ℂ F
  let inv := hf.localInverse f J a
  have hinv : HasStrictFDerivAt inv (J.symm : (ℂ × F) →L[ℂ] E) (0,0) := by
    simpa only [hf0] using hf.to_localInverse
  have hinv0 : inv (0,0)=a := by simpa only [hf0] using hf.localInverse_apply_image
  have hgraph : ∀ᶠ t in atTop, inv (h t,0)=p t := by
    filter_upwards [hp.eventually hf.eventually_left_inverse,hres] with t ht hr
    rw [← hr]
    exact ht
  have hd : HasDerivAt (fun z : ℂ => W (inv (z,0))) (D (J.symm (1,0))) 0 := by
    have hw' : HasFDerivAt W D (inv (0,0)) := by simpa only [hinv0] using hW.hasFDerivAt
    have hi : HasFDerivAt (fun z : ℂ => (z,(0:F))) ins 0 := ins.hasFDerivAt
    have hcomp := (hw'.comp (0,0) hinv.hasFDerivAt).comp (f := fun z : ℂ => (z,(0:F))) 0 hi
    have hcomp' := hcomp.hasDerivAt
    simpa only [hinv0,ins,ContinuousLinearMap.inl_apply,ContinuousLinearMap.coe_comp,
      Function.comp_apply] using hcomp'
  have hz : Tendsto h atTop (𝓝[≠] (0:ℂ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hh,Eventually.of_forall hne⟩
  have hs := hd.tendsto_slope.comp hz
  have hs' : Tendsto (fun t => W (p t)/h t) atTop (𝓝 (D (J.symm (1,0)))) := by
    apply hs.congr'
    filter_upwards [hgraph] with t ht
    simp only [Function.comp_apply,slope,sub_zero,hinv0,hW0,ht,smul_eq_mul,vsub_eq_sub]
    ring
  exact tendsto_nhds_unique hs' hWt

end
end CentralConfigurations.FiveBody.D2.Regular


