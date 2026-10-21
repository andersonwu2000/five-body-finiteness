import CentralConfigurations.FiveBody.D2Jacobian.ShapeDerivative
import CentralConfigurations.FiveBody.D2Jacobian.CrossSums

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem bilinear_linear_right (n t d f : Fin 3 → ℂ) (a b : ℂ) :
    bilinear n t (fun i => a*d i+b*f i)=a*bilinear n t d+b*bilinear n t f := by
  simp only [bilinear,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _; ring

def bilinearDerivative (n t : Fin 3 → ℂ) (f : Fin 3 → ChartSpace →L[ℂ] ℂ) :
    ChartSpace →L[ℂ] ℂ := ∑ i, (n i*t i) • f i

@[simp] theorem bilinearDerivative_apply (n t : Fin 3 → ℂ)
    (f : Fin 3 → ChartSpace →L[ℂ] ℂ) (v : ChartSpace) :
    bilinearDerivative n t f v=bilinear n t (fun i => f i v) := by
  simp [bilinearDerivative,bilinear,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

def shapeNorm : ℂ := bilinear (shapeMass m) (leadingD s) (leadingD s)
def transverseNorm : ℂ := bilinear (shapeMass m) (leadingE s) (leadingE s)

theorem shapeNorm_ne : shapeNorm s≠0 := normalized_nonisotropic s

include hm in
theorem leading_orthogonal : bilinear (shapeMass m) (leadingD s) (leadingE s)=0 :=
  transverse_orthogonal (shapeMass m) (leadingD s)
    (fun i => Complex.ofReal_ne_zero.mpr (ne_of_gt (hm (tripleIndex i))))

include hm in
theorem leading_orthogonal_reverse : bilinear (shapeMass m) (leadingE s) (leadingD s)=0 := by
  have hh := leading_orthogonal s hm
  simpa only [bilinear,mul_assoc,mul_left_comm,mul_comm] using hh

include hm in
theorem transverseNorm_ne : transverseNorm s≠0 := by
  have hn (i : Fin 3) : shapeMass m i≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (hm (tripleIndex i)))
  have hB : shapeMass m 0+shapeMass m 1+shapeMass m 2≠0 := by
    exact_mod_cast ne_of_gt (add_pos (add_pos (hm 0) (hm 1)) (hm 2))
  dsimp [transverseNorm,leadingE]
  rw [transverse_norm (shapeMass m) (leadingD s) hn
    (show weightedCenter (shapeMass m) (leadingD s)=0 from (normalizedTriangle s).mass_center_w)]
  exact div_ne_zero (mul_ne_zero hB (shapeNorm_ne s)) (mul_ne_zero (mul_ne_zero (hn 0) (hn 1)) (hn 2))

def longitudinalRow : ChartSpace →L[ℂ] ℂ :=
  shapeNorm s • ((3/(2*normalizedKappa s)) • chartCoord 1-(3*leadingE s 2/2) • chartCoord 3)
def transverseZRow : ChartSpace →L[ℂ] ℂ :=
  transverseNorm s • ((1+transverseEigenvalue s.triangle/2) • chartCoord 2+
    (3*normalizedKappa s*transverseEigenvalue s.triangle/2) • chartCoord 3)-
    bilinear (shapeMass m) (leadingE s) (jacobianResponse s e) • hCoord
def transverseWRow : ChartSpace →L[ℂ] ℂ :=
  transverseNorm s • ((3*transverseEigenvalue s.triangle/(2*normalizedKappa s)) • chartCoord 2+
    (1+transverseEigenvalue s.triangle/2) • chartCoord 3)

theorem shapeWDerivative_apply (i : Fin 3) (v : ChartSpace) :
    shapeWDerivative s i v=
      (3*v.2 1/(2*normalizedKappa s)-3*leadingE s 2*v.2 3/2)*leadingD s i+
      (3*transverseEigenvalue s.triangle*v.2 2/(2*normalizedKappa s)+
        (1+transverseEigenvalue s.triangle/2)*v.2 3)*leadingE s i := by
  simp only [shapeWDerivative,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,chartCoord_apply,smul_eq_mul]
  ring

theorem shapeZDerivative_apply (i : Fin 3) (v : ChartSpace) :
    shapeZDerivative s i v=
      (3*v.2 1/2-3*normalizedKappa s*leadingE s 2*v.2 3/2)*leadingD s i+
      ((1+transverseEigenvalue s.triangle/2)*v.2 2+
        3*normalizedKappa s*transverseEigenvalue s.triangle*v.2 3/2)*leadingE s i := by
  simp only [shapeZDerivative,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,chartCoord_apply,smul_eq_mul]
  ring

include hm in
theorem longitudinalRow_eq : longitudinalRow s=
    bilinearDerivative (shapeMass m) (leadingD s) (shapeWDerivative s) := by
  apply ContinuousLinearMap.ext; intro v
  rw [bilinearDerivative_apply]
  simp_rw [shapeWDerivative_apply]
  rw [bilinear_linear_right,leading_orthogonal s hm]
  simp only [longitudinalRow,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sub_apply,
    chartCoord_apply,smul_eq_mul,shapeNorm,mul_zero,add_zero]
  ring

include hm in
theorem transverseWRow_eq : transverseWRow s=
    bilinearDerivative (shapeMass m) (leadingE s) (shapeWDerivative s) := by
  apply ContinuousLinearMap.ext; intro v
  rw [bilinearDerivative_apply]
  simp_rw [shapeWDerivative_apply]
  rw [bilinear_linear_right,leading_orthogonal_reverse s hm]
  simp only [transverseWRow,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    chartCoord_apply,smul_eq_mul,transverseNorm,mul_zero,zero_add]
  ring

include hm in
theorem transverseZRow_eq : transverseZRow s e=
    bilinearDerivative (shapeMass m) (leadingE s)
      (fun i => shapeZDerivative s i-jacobianResponse s e i • hCoord) := by
  apply ContinuousLinearMap.ext; intro v
  rw [bilinearDerivative_apply]
  simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,hCoord_apply]
  have he : (fun i => shapeZDerivative s i v-jacobianResponse s e i*v.1)=
      (fun i => shapeZDerivative s i v+(-v.1)*jacobianResponse s e i) := by
    funext i; ring
  have hb := bilinear_linear_right (shapeMass m) (leadingE s)
    (fun i => shapeZDerivative s i v) (jacobianResponse s e) 1 (-v.1)
  simp only [one_mul] at hb
  rw [he,hb]
  simp_rw [shapeZDerivative_apply]
  rw [bilinear_linear_right,leading_orthogonal_reverse s hm]
  simp only [transverseZRow,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,chartCoord_apply,hCoord_apply,smul_eq_mul,transverseNorm,mul_zero,zero_add]
  ring

end
end CentralConfigurations.FiveBody.D2.Regular

