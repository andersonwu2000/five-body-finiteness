import CentralConfigurations.FiveBody.D2Jacobian.CrossDerivative

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section

theorem scalar_div_strictFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : E → ℂ} {f' : E →L[ℂ] ℂ} {x : E}
    (hf : HasStrictFDerivAt f f' x) (b : ℂ) :
    HasStrictFDerivAt (fun y => f y/b) ((1/b) • f') x := by
  simpa only [div_eq_mul_inv,one_mul] using hf.mul_const b⁻¹

end
end CentralConfigurations.FiveBody.D2.Regular
