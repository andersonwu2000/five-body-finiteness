import CentralConfigurations.FiveBody.D2Jacobian.Coordinates

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators

theorem forceZ_strictFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c d : E → ℂ} {c' d' : E →L[ℂ] ℂ} {x : E} {c0 d0 r : ℂ}
    (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x)
    (hcv : c x=c0) (hdv : d x=d0) (hc0 : c0≠0) (hd0 : d0≠0) :
    HasStrictFDerivAt (fun y => rootSheet r (c0*d0) (c y*d y)^3*c y)
      ((-r^3/2) • c'-(3*c0*r^3/(2*d0)) • d') x := by
  have he : (c0/d0)*d0^2=c0*d0 := by field_simp
  have hh := force_strictFDerivAt hc hd (k := c0/d0) (w := d0) (r := r)
    (by rw [hcv]; field_simp) hdv (div_ne_zero hc0 hd0) hd0
  rw [he] at hh
  convert hh using 1
  ext y
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
  field_simp

theorem forceW_strictFDerivAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {c d : E → ℂ} {c' d' : E →L[ℂ] ℂ} {x : E} {c0 d0 r : ℂ}
    (hc : HasStrictFDerivAt c c' x) (hd : HasStrictFDerivAt d d' x)
    (hcv : c x=c0) (hdv : d x=d0) (hc0 : c0≠0) (hd0 : d0≠0) :
    HasStrictFDerivAt (fun y => rootSheet r (c0*d0) (c y*d y)^3*d y)
      ((-3*d0*r^3/(2*c0)) • c'-(r^3/2) • d') x := by
  have hh := forceZ_strictFDerivAt hd hc hdv hcv hd0 hc0 (r := r)
  convert hh using 1
  · ext y; simp only [mul_comm]
  · ext y
    simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

include hm in
theorem crossRoot_strictFDerivAt (p : Fin 2) (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelCrossRoot s e v.1 v.2 p i)
      ((-(s.cross p i/e.ratio)/(2*leadingD s i)) • dDerivative s i)
      (0,baseCoordinates s e) := by
  have hP := cross_base_product_ne s e hm p i
  have ha : modelA (m := m) p≠0 := by
    intro hh; apply hP; rw [hh,neg_zero,zero_mul]
  have hd : leadingD s i≠0 := by
    intro hh; apply hP; rw [hh,mul_zero]
  have hp := (modelZeta_strictFDerivAt s e p i).mul (modelChi_strictFDerivAt s e p i)
  have he : -modelA (m := m) p*leadingD s i=
      modelZeta s 0 (baseCoordinates s e) p i*modelChi s 0 (baseCoordinates s e) p i := by
    rw [modelZeta_base,modelChi_base]
  have hr := (rootSheet_strictDeriv (r0 := s.cross p i/e.ratio) hP).comp_hasStrictFDerivAt_of_eq (0,baseCoordinates s e) hp he
  convert hr using 1
  apply ContinuousLinearMap.ext; intro v
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.zero_apply,modelZeta_base,modelChi_base]
  field_simp [ha,hd]
  ring

include hm in
theorem crossForceZ_strictFDerivAt (p : Fin 2) (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelCrossRoot s e v.1 v.2 p i^3*
      modelZeta s v.1 v.2 p i)
      ((3*modelA (m := m) p*(s.cross p i/e.ratio)^3/(2*leadingD s i)) • dDerivative s i)
      (0,baseCoordinates s e) := by
  have hP := cross_base_product_ne s e hm p i
  have ha : -modelA (m := m) p≠0 := (mul_ne_zero_iff.mp hP).1
  have hd : leadingD s i≠0 := (mul_ne_zero_iff.mp hP).2
  have hh := forceZ_strictFDerivAt (modelZeta_strictFDerivAt s e p i)
    (modelChi_strictFDerivAt s e p i) (modelZeta_base s e p i) (modelChi_base s e p i) ha hd
    (r := s.cross p i/e.ratio)
  convert hh using 1
  apply ContinuousLinearMap.ext; intro v
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply]
  ring

include hm in
theorem crossForceW_strictFDerivAt (p : Fin 2) (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelCrossRoot s e v.1 v.2 p i^3*
      modelChi s v.1 v.2 p i)
      ((-(s.cross p i/e.ratio)^3/2) • dDerivative s i)
      (0,baseCoordinates s e) := by
  have hP := cross_base_product_ne s e hm p i
  have ha : -modelA (m := m) p≠0 := (mul_ne_zero_iff.mp hP).1
  have hd : leadingD s i≠0 := (mul_ne_zero_iff.mp hP).2
  have hh := forceW_strictFDerivAt (modelZeta_strictFDerivAt s e p i)
    (modelChi_strictFDerivAt s e p i) (modelZeta_base s e p i) (modelChi_base s e p i) ha hd
    (r := s.cross p i/e.ratio)
  convert hh using 1
  apply ContinuousLinearMap.ext; intro v
  simp only [ContinuousLinearMap.smul_apply,smul_eq_mul,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply]
  ring

end
end CentralConfigurations.FiveBody.D2.Regular


