import CentralConfigurations.FiveBody.D2Resonance.GapPolynomial
import CentralConfigurations.FiveBody.D2Exceptional.ResonancePositiveFiber

noncomputable section
open Polynomial
namespace CentralConfigurations.FiveBody.D2.Resonance
open Exceptional
set_option maxHeartbeats 2000000

theorem positive_quintic_expand {R : Type*} [CommRing R] (a b c : R) :
    gapPolynomial a b c 1 1 =
      -C (a+b)*X^5+C (2*a+3*b)*X^4-C (a+3*b)*X^3+
      C (a+2*b+3*c)*X^2-C (2*a+3*c)*X+C (a+c) := by
  simp only [gapPolynomial,map_add,map_mul,map_ofNat,map_one]
  ring

theorem conjugate_factor_expand {R : Type*} [CommRing R] (M u v r : R) :
    C (-M)*(X^2-C u*X+C v)^2*(X-C r) =
      -C M*X^5+C (M*(r+2*u))*X^4-C (M*(2*r*u+u^2+2*v))*X^3+
      C (M*(r*u^2+2*r*v+2*u*v))*X^2-C (M*(2*r*u*v+v^2))*X+
      C (M*r*v^2) := by
  simp only [map_neg,map_add,map_mul,map_pow,map_ofNat]
  ring

theorem coefficient_ideal_of_factor (a b c u v r : ℝ) (hm : a+b=1)
    (hf : gapPolynomial a b c 1 1 =
      -(X^2-C u*X+C v)^2*(X-C r)) :
    F1 u v r=0 ∧ F2 u v r=0 ∧ F3 u v r=0 := by
  have hf' : gapPolynomial a b c 1 1 =
      C (-1)*(X^2-C u*X+C v)^2*(X-C r) := by simpa using hf
  rw [positive_quintic_expand,conjugate_factor_expand] at hf'
  have h4 := congrArg (fun p : ℝ[X] => p.coeff 4) hf'
  have h3 := congrArg (fun p : ℝ[X] => p.coeff 3) hf'
  have h2 := congrArg (fun p : ℝ[X] => p.coeff 2) hf'
  have h1 := congrArg (fun p : ℝ[X] => p.coeff 1) hf'
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hf'
  simp only [neg_mul,coeff_add,coeff_sub,coeff_neg,coeff_C_mul_X_pow,
    coeff_C_mul_X,coeff_C] at h4 h3 h2 h1 h0
  norm_num at h4 h3 h2 h1 h0
  dsimp [F1,F2,F3]
  constructor
  · linear_combination -h3-2*h4+3*hm
  constructor
  · linear_combination -h2+3*h0+4*h4-10*hm
  · linear_combination h1+3*h0+h4-3*hm

theorem normalized_mass_rows_of_factor (a b c u v r : ℝ) (hm : a+b=1)
    (hf : gapPolynomial a b c 1 1 =
      -(X^2-C u*X+C v)^2*(X-C r)) :
    a=3-r-2*u ∧ c=r*v^2-a := by
  have hf' : gapPolynomial a b c 1 1 =
      C (-1)*(X^2-C u*X+C v)^2*(X-C r) := by simpa using hf
  rw [positive_quintic_expand,conjugate_factor_expand] at hf'
  have h4 := congrArg (fun p : ℝ[X] => p.coeff 4) hf'
  have h0 := congrArg (fun p : ℝ[X] => p.coeff 0) hf'
  simp only [neg_mul,coeff_add,coeff_sub,coeff_neg,coeff_C_mul_X_pow,
    coeff_C_mul_X,coeff_C] at h4 h0
  norm_num at h4 h0
  constructor
  · linear_combination -h4+3*hm
  · linear_combination h0

theorem gapPolynomial_scale {R : Type*} [CommRing R] (a b c s13 s23 t : R) :
    gapPolynomial (t*a) (t*b) (t*c) s13 s23 = C t*gapPolynomial a b c s13 s23 := by
  simp only [gapPolynomial,map_add,map_mul]
  ring

end CentralConfigurations.FiveBody.D2.Resonance
