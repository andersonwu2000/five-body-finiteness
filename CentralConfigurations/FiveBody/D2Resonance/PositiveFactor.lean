import CentralConfigurations.FiveBody.D2Resonance.ConjugateFactor
import CentralConfigurations.FiveBody.D2Resonance.CoefficientRows

noncomputable section
open Polynomial
namespace CentralConfigurations.FiveBody.D2.Resonance
open Exceptional
set_option maxHeartbeats 2000000

theorem positive_quintic_natDegree (a b c : ℝ) (hm : a+b≠0) :
    (gapPolynomial a b c 1 1).natDegree=5 := by
  have hdeg : (gapPolynomial a b c 1 1).natDegree≤5 := by
    rw [positive_quintic_expand]
    compute_degree!
  apply natDegree_eq_of_le_of_coeff_ne_zero hdeg
  rw [positive_quintic_expand]
  simp only [neg_mul,coeff_add,coeff_sub,coeff_neg,coeff_C_mul_X_pow,
    coeff_C_mul_X,coeff_C]
  norm_num
  simpa only [neg_add,add_comm] using neg_ne_zero.mpr hm

theorem positive_quintic_leadingCoeff (a b c : ℝ) (hm : a+b≠0) :
    (gapPolynomial a b c 1 1).leadingCoeff=-(a+b) := by
  rw [leadingCoeff,positive_quintic_natDegree a b c hm,positive_quintic_expand]
  simp only [neg_mul,coeff_add,coeff_sub,coeff_neg,coeff_C_mul_X_pow,
    coeff_C_mul_X,coeff_C]
  norm_num

theorem positive_repeated_factor (a b c : ℝ) (x : ℂ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hroot : (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) 1 1).eval x=0)
    (hderiv : (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) 1 1).derivative.eval x=0) :
    ∃ r : ℝ, 1<r ∧
      gapPolynomial a b c 1 1 =
        C (-(a+b))*(realPairQuadratic x)^2*(X-C r) := by
  have hm : a+b≠0 := ne_of_gt (by linarith)
  have hx := positive_quintic_repeated_nonreal a b c x ha hb hc hroot hderiv
  have hmap := gapPolynomial_map Complex.ofRealHom a b c 1 1
  simp only [Complex.ofRealHom_eq_coe,Complex.ofReal_one] at hmap
  rw [← hmap] at hroot hderiv
  obtain ⟨r,hf⟩ := quintic_conjugate_factor (gapPolynomial a b c 1 1)
    (positive_quintic_natDegree a b c hm) (-(a+b))
    (positive_quintic_leadingCoeff a b c hm) x hx hroot hderiv
  have hr : (gapPolynomial a b c 1 1).eval r=0 := by rw [hf]; simp
  exact ⟨r,positive_quintic_root_gt_one a b c r ha hb hc hr,hf⟩

theorem positive_normalized_factor (a b c : ℝ) (x : ℂ) (r : ℝ) (hm : a+b≠0)
    (hf : gapPolynomial a b c 1 1 =
      C (-(a+b))*(realPairQuadratic x)^2*(X-C r)) :
    gapPolynomial (a/(a+b)) (b/(a+b)) (c/(a+b)) 1 1 =
      -(realPairQuadratic x)^2*(X-C r) := by
  have hs := gapPolynomial_scale a b c 1 1 (1/(a+b))
  have hA : 1/(a+b)*a=a/(a+b) := by ring
  have hB : 1/(a+b)*b=b/(a+b) := by ring
  have hC : 1/(a+b)*c=c/(a+b) := by ring
  rw [hA,hB,hC] at hs
  rw [hs,hf]
  have hu : C (1/(a+b))*C (a+b)=(1:ℝ[X]) := by
    rw [← map_mul,one_div_mul_cancel hm,map_one]
  rw [map_neg]
  calc
    C (1/(a+b)) * (-C (a+b)*(realPairQuadratic x)^2*(X-C r)) =
        -(C (1/(a+b))*C (a+b))*(realPairQuadratic x)^2*(X-C r) := by ring
    _ = _ := by rw [hu]; ring

theorem positive_repeated_coefficient_fiber (a b c : ℝ) (x : ℂ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hroot : (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) 1 1).eval x=0)
    (hderiv : (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) 1 1).derivative.eval x=0) :
    2*x.re=Real.sqrt 2-1 ∧ Complex.normSq x=Real.sqrt 2-1 := by
  obtain ⟨r,hr,hf⟩ := positive_repeated_factor a b c x ha hb hc hroot hderiv
  have hm : a+b≠0 := ne_of_gt (by linarith)
  have hfn := positive_normalized_factor a b c x r hm hf
  have hab : a/(a+b)+b/(a+b)=1 := by rw [← add_div,div_self hm]
  have hv : 0<Complex.normSq x := Complex.normSq_pos.mpr (by
    intro he
    have hx := positive_quintic_repeated_nonreal a b c x ha hb hc hroot hderiv
    exact hx (by simp [he]))
  change gapPolynomial (a/(a+b)) (b/(a+b)) (c/(a+b)) 1 1 =
    -(X^2-C (2*x.re)*X+C (Complex.normSq x))^2*(X-C r) at hfn
  obtain ⟨h1,h2,h3⟩ := coefficient_ideal_of_factor _ _ _ _ _ _ hab hfn
  obtain ⟨_,hu,hv'⟩ := coefficient_positive_fiber hr hv h1 h2 h3
  exact ⟨hu,hv'⟩

end CentralConfigurations.FiveBody.D2.Resonance
