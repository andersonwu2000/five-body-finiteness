import CentralConfigurations.FiveBody.D2Exceptional.GapClear
import CentralConfigurations.FiveBody.D2Exceptional.GapDerivative
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Calculus.Deriv.Polynomial

noncomputable section
open Polynomial
namespace CentralConfigurations.FiveBody.D2.Resonance
open Exceptional
set_option maxHeartbeats 2000000

def gapPolynomial {R : Type*} [CommRing R] (a b c s13 s23 : R) : R[X] :=
  C s13 * (C (a+c)-C c*X)*(X-1)^2 + C b*X^2*((X-1)^2+C s23) +
    C (c*s23)*X^3-C (a+b)*X^3*(X-1)^2

theorem gapPolynomial_eval (a b c s13 s23 x : ℂ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    (gapPolynomial a b c s13 s23).eval x =
      x^2*(x-1)^2*gapEuler a b c x s13 s23 := by
  simp only [gapPolynomial,eval_add,eval_sub,eval_mul,eval_pow,eval_C,eval_X,eval_one]
  dsimp [gapEuler,gapLambda]
  field_simp [hx,sub_ne_zero.mpr hx1]
  ring

theorem gapPolynomial_derivative_eval (a b c s13 s23 x : ℂ)
    (hx : x ≠ 0) (hx1 : x ≠ 1) :
    (gapPolynomial a b c s13 s23).derivative.eval x =
      (2*x*(x-1)^2+2*x^2*(x-1))*gapEuler a b c x s13 s23 +
      x^2*(x-1)^2*(gapLambda a b c x s13 s23-2*gapTrace a b c x s13 s23) := by
  simp only [gapPolynomial,derivative_add,derivative_sub,derivative_mul,
    derivative_pow,derivative_C,derivative_X,derivative_one,eval_add,eval_sub,
    eval_mul,eval_pow,eval_C,eval_X,eval_one,eval_zero]
  dsimp [gapEuler,gapLambda,gapTrace]
  field_simp [hx,sub_ne_zero.mpr hx1]
  ring

theorem GapData.polynomial_and_derivative_zero {mass : Fin 3 → ℂ}
    {r : ZWSystem ℂ 3 mass} (d : GapData r)
    (hell : transverseEigenvalue r = -(1/2 : ℂ)) :
    (gapPolynomial (mass 0) (mass 1) (mass 2) d.sign13 d.sign23).eval d.x=0 ∧
    (gapPolynomial (mass 0) (mass 1) (mass 2) d.sign13 d.sign23).derivative.eval d.x=0 := by
  have he := d.euler_zero
  have ht := d.trace
  change transverseEigenvalue r =
    gapTrace (mass 0) (mass 1) (mass 2) d.x d.sign13 d.sign23/d.lam-1 at ht
  rw [hell] at ht
  field_simp [d.lam_ne_zero] at ht
  have hs : gapLambda (mass 0) (mass 1) (mass 2) d.x d.sign13 d.sign23-
      2*gapTrace (mass 0) (mass 1) (mass 2) d.x d.sign13 d.sign23=0 := by
    rw [← d.original_rows.1]
    linear_combination ht
  constructor
  · rw [gapPolynomial_eval _ _ _ _ _ _ d.x_ne_zero d.x_ne_one,he,mul_zero]
  · rw [gapPolynomial_derivative_eval _ _ _ _ _ _ d.x_ne_zero d.x_ne_one,he,hs]
    ring

theorem gapPolynomial_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (a b c s13 s23 : R) :
    (gapPolynomial a b c s13 s23).map f =
      gapPolynomial (f a) (f b) (f c) (f s13) (f s23) := by
  simp [gapPolynomial]

theorem gapPolynomial_eval_cast (a b c s13 s23 x : ℝ) :
    (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) (s13:ℂ) (s23:ℂ)).eval (x:ℂ) =
      (((gapPolynomial a b c s13 s23).eval x : ℝ) : ℂ) := by
  simp [gapPolynomial]

theorem gapPolynomial_derivative_eval_cast (a b c s13 s23 x : ℝ) :
    (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) (s13:ℂ) (s23:ℂ)).derivative.eval (x:ℂ) =
      (((gapPolynomial a b c s13 s23).derivative.eval x : ℝ) : ℂ) := by
  have h := gapPolynomial_map Complex.ofRealHom a b c s13 s23
  change (gapPolynomial a b c s13 s23).map Complex.ofRealHom =
    gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) (s13:ℂ) (s23:ℂ) at h
  rw [← h,derivative_map]
  exact eval_map_apply Complex.ofRealHom x

end CentralConfigurations.FiveBody.D2.Resonance
