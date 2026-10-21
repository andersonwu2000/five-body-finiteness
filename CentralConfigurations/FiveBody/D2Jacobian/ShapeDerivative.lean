import CentralConfigurations.FiveBody.D2Jacobian.CrossDerivative

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

def shapeZDerivative (i : Fin 3) : ChartSpace →L[ℂ] ℂ :=
  leadingD s i • ((3/2:ℂ) • chartCoord 1-(3*normalizedKappa s*leadingE s 2/2) • chartCoord 3)+
  leadingE s i • ((1+transverseEigenvalue s.triangle/2) • chartCoord 2+
    (3*normalizedKappa s*transverseEigenvalue s.triangle/2) • chartCoord 3)

def shapeWDerivative (i : Fin 3) : ChartSpace →L[ℂ] ℂ :=
  leadingD s i • ((3/(2*normalizedKappa s)) • chartCoord 1-(3*leadingE s 2/2) • chartCoord 3)+
  leadingE s i • ((3*transverseEigenvalue s.triangle/(2*normalizedKappa s)) • chartCoord 2+
    (1+transverseEigenvalue s.triangle/2) • chartCoord 3)

theorem triangleForceZ_strictFDerivAt (i j : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelTriangleRoot s v.2 i j^3*
      (modelC s v.2 i-modelC s v.2 j))
      ((-s.triangle.delta i j^3/2) • (cDerivative s i-cDerivative s j)-
        (3*normalizedKappa s*s.triangle.delta i j^3/2) • (dDerivative s i-dDerivative s j))
      (0,baseCoordinates s e) := by
  by_cases hij : i=j
  · subst j
    convert hasStrictFDerivAt_const (𝕜 := ℂ) (0:ℂ) ((0,baseCoordinates s e):ChartSpace) using 1
    · funext v; simp [modelTriangleRoot]
    · apply ContinuousLinearMap.ext; intro v; simp
  · have hd : leadingD s i-leadingD s j≠0 := (normalizedTriangle s).w_separation_ne_zero hij
    have hc : modelC s (baseCoordinates s e) i-modelC s (baseCoordinates s e) j=
        normalizedKappa s*(leadingD s i-leadingD s j) := by
      rw [base_modelC,base_modelC,normalized_proportional,normalized_proportional]
      dsimp [leadingD]; ring
    have hP : ((normalizedTriangle s).z i-(normalizedTriangle s).z j)*
        (leadingD s i-leadingD s j)=normalizedKappa s*(leadingD s i-leadingD s j)^2 := by
      rw [normalized_proportional,normalized_proportional]; dsimp [leadingD]; ring
    have hh := force_strictFDerivAt ((modelC_strictFDerivAt s e i).sub
      (modelC_strictFDerivAt s e j)) ((modelD_strictFDerivAt s e i).sub
      (modelD_strictFDerivAt s e j)) hc
      (by change modelD s (baseCoordinates s e) i-modelD s (baseCoordinates s e) j=_
          rw [base_modelD,base_modelD]; rfl) (normalized_kappa_ne s) hd
      (r := s.triangle.delta i j)
    simpa only [modelTriangleRoot,if_neg hij,hP] using hh

theorem triangleForceW_strictFDerivAt (i j : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelTriangleRoot s v.2 i j^3*
      (modelD s v.2 i-modelD s v.2 j))
      ((-3*s.triangle.delta i j^3/(2*normalizedKappa s)) • (cDerivative s i-cDerivative s j)-
        (s.triangle.delta i j^3/2) • (dDerivative s i-dDerivative s j))
      (0,baseCoordinates s e) := by
  by_cases hij : i=j
  · subst j
    convert hasStrictFDerivAt_const (𝕜 := ℂ) (0:ℂ) ((0,baseCoordinates s e):ChartSpace) using 1
    · funext v; simp [modelTriangleRoot]
    · apply ContinuousLinearMap.ext; intro v; simp
  · have hd : leadingD s i-leadingD s j≠0 := (normalizedTriangle s).w_separation_ne_zero hij
    have hc : modelC s (baseCoordinates s e) i-modelC s (baseCoordinates s e) j=
        normalizedKappa s*(leadingD s i-leadingD s j) := by
      rw [base_modelC,base_modelC,normalized_proportional,normalized_proportional]
      dsimp [leadingD]; ring
    have hP : ((normalizedTriangle s).z i-(normalizedTriangle s).z j)*
        (leadingD s i-leadingD s j)=(normalizedKappa s*(leadingD s i-leadingD s j))*
        (leadingD s i-leadingD s j) := by
      rw [normalized_proportional,normalized_proportional]; dsimp [leadingD]; ring
    have hh := forceW_strictFDerivAt ((modelC_strictFDerivAt s e i).sub
      (modelC_strictFDerivAt s e j)) ((modelD_strictFDerivAt s e i).sub
      (modelD_strictFDerivAt s e j)) hc
      (by change modelD s (baseCoordinates s e) i-modelD s (baseCoordinates s e) j=_
          rw [base_modelD,base_modelD]; rfl)
      (mul_ne_zero (normalized_kappa_ne s) hd) hd (r := s.triangle.delta i j)
    rw [← hP] at hh
    convert hh using 1
    · funext v; simp only [modelTriangleRoot,if_neg hij,Pi.sub_apply]
    · apply ContinuousLinearMap.ext; intro v
      simp only [ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
      field_simp

theorem leading_laplacian_d (i : Fin 3) :
    laplacian (shapeMass m) s.triangle.delta (leadingD s) i=leadingD s i := by
  exact ((normalizedTriangle s).force_w i).symm

include hm in
theorem leading_laplacian_e (i : Fin 3) :
    laplacian (shapeMass m) s.triangle.delta (leadingE s) i=
      transverseEigenvalue s.triangle*leadingE s i := by
  exact actual_transverse_eigenvector (normalizedTriangle s)
    (fun j => Complex.ofReal_ne_zero.mpr (ne_of_gt (hm (tripleIndex j)))) i

include hm in
theorem modelFz_strictFDerivAt (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelFz s v.2 i)
      (shapeZDerivative s i) (0,baseCoordinates s e) := by
  have hh := (modelC_strictFDerivAt s e i).sub (HasStrictFDerivAt.fun_sum
    (u := Finset.univ) (fun j _ => (triangleForceZ_strictFDerivAt s e i j).const_mul (shapeMass m j)))
  convert hh using 1
  · funext v; simp only [modelFz]; congr 1; apply Finset.sum_congr rfl
    intro j _; ring
  · apply ContinuousLinearMap.ext; intro v
    have hd := leading_laplacian_d s i
    have he := leading_laplacian_e s hm i
    simp only [laplacian,Fin.sum_univ_succ] at hd he
    simp only [shapeZDerivative,cDerivative,dDerivative,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
      smul_eq_mul,chartCoord_apply,Fin.sum_univ_succ]
    linear_combination -(v.2 1/2-3*normalizedKappa s*leadingE s 2*v.2 3/2)*hd-
      (v.2 2/2+3*normalizedKappa s*v.2 3/2)*he

include hm in
theorem modelFw_strictFDerivAt (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelFw s v.2 i)
      (shapeWDerivative s i) (0,baseCoordinates s e) := by
  have hh := (modelD_strictFDerivAt s e i).sub (HasStrictFDerivAt.fun_sum
    (u := Finset.univ) (fun j _ => (triangleForceW_strictFDerivAt s e i j).const_mul (shapeMass m j)))
  convert hh using 1
  · funext v; simp only [modelFw]; congr 1; apply Finset.sum_congr rfl
    intro j _; ring
  · apply ContinuousLinearMap.ext; intro v
    have hd := leading_laplacian_d s i
    have he := leading_laplacian_e s hm i
    simp only [laplacian,Fin.sum_univ_succ] at hd he
    simp only [shapeWDerivative,cDerivative,dDerivative,ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,ContinuousLinearMap.sum_apply,
      smul_eq_mul,chartCoord_apply,Fin.sum_univ_succ]
    field_simp [normalized_kappa_ne s]
    linear_combination -(3*v.2 1- normalizedKappa s*leadingE s 2*v.2 3)*hd-
      (3*v.2 2+normalizedKappa s*v.2 3)*he

end
end CentralConfigurations.FiveBody.D2.Regular


