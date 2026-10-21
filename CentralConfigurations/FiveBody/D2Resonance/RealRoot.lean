import CentralConfigurations.FiveBody.D2Resonance.GapPolynomial

noncomputable section
open Polynomial
namespace CentralConfigurations.FiveBody.D2.Resonance
set_option maxHeartbeats 2000000

theorem positive_quintic_factor (a b c x : ℝ) :
    (gapPolynomial a b c 1 1).eval x =
      -a*(x-1)^3*(x^2+x+1)-b*x^2*(x-2)*(x^2-x+1)+c*(3*x^2-3*x+1) := by
  simp [gapPolynomial]
  ring

theorem positive_quintic_pos_of_le_one (a b c x : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hx : x≤1) :
    0 < (gapPolynomial a b c 1 1).eval x := by
  rw [positive_quintic_factor]
  have h1 : 0 < x^2+x+1 := by nlinarith [sq_nonneg (x+1/2)]
  have h2 : 0 < x^2-x+1 := by nlinarith [sq_nonneg (x-1/2)]
  have h3 : 0 < 3*x^2-3*x+1 := by nlinarith [sq_nonneg (x-1/2)]
  have hpow : (x-1)^3≤0 := (by decide : Odd 3).pow_nonpos (by linarith)
  have ht1 : 0 ≤ -a*(x-1)^3*(x^2+x+1) :=
    mul_nonneg (mul_nonneg_of_nonpos_of_nonpos (by linarith) hpow) h1.le
  have ht2 : 0 ≤ -b*x^2*(x-2)*(x^2-x+1) := by
    have : -b*x^2 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg x)
    exact mul_nonneg (mul_nonneg_of_nonpos_of_nonpos this (by linarith)) h2.le
  nlinarith [mul_pos hc h3]

theorem positive_quintic_root_gt_one (a b c x : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hroot : (gapPolynomial a b c 1 1).eval x=0) : 1<x := by
  by_contra! h
  have := positive_quintic_pos_of_le_one a b c x ha hb hc h
  linarith

theorem positive_quintic_shift (a b c y : ℝ) :
    (gapPolynomial a b c 1 1).eval (1+y) =
      -(a+b)*y^5-(3*a+2*b)*y^4-(3*a+b)*y^3+
        (b+3*c)*y^2+(2*b+3*c)*y+(b+c) := by
  simp [gapPolynomial]
  ring

theorem positive_quintic_derivative_certificate (a b c y : ℝ) :
    y*(gapPolynomial a b c 1 1).derivative.eval (1+y)-
      2*(gapPolynomial a b c 1 1).eval (1+y) =
      -3*(a+b)*y^5-2*(3*a+2*b)*y^4-(3*a+b)*y^3-
        (2*b+3*c)*y-2*(b+c) := by
  simp [gapPolynomial,derivative_mul,derivative_pow]
  ring

theorem positive_quintic_real_simple (a b c x : ℝ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hroot : (gapPolynomial a b c 1 1).eval x=0) :
    (gapPolynomial a b c 1 1).derivative.eval x≠0 := by
  have hx := positive_quintic_root_gt_one a b c x ha hb hc hroot
  let y := x-1
  have hy : 0<y := by dsimp [y]; linarith
  have he := positive_quintic_derivative_certificate a b c y
  have hshift : 1+y=x := by dsimp [y]; ring
  rw [hshift,hroot] at he
  have h5 : 0 < 3*(a+b)*y^5 := by positivity
  have h4 : 0 ≤ 2*(3*a+2*b)*y^4 := by positivity
  have h3 : 0 ≤ (3*a+b)*y^3 := by positivity
  have h1 : 0 ≤ (2*b+3*c)*y := by positivity
  have h0 : 0 ≤ 2*(b+c) := by positivity
  intro hd
  rw [hd] at he
  linarith

theorem positive_quintic_repeated_nonreal (a b c : ℝ) (x : ℂ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hroot : (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) 1 1).eval x=0)
    (hderiv : (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) 1 1).derivative.eval x=0) :
    x.im≠0 := by
  intro him
  have hx : x=(x.re:ℂ) := by apply Complex.ext <;> simp [him]
  rw [hx] at hroot hderiv
  have hr : (gapPolynomial a b c 1 1).eval x.re=0 := by
    apply Complex.ofReal_injective
    simpa only [← gapPolynomial_eval_cast,Complex.ofReal_one,Complex.ofReal_zero] using hroot
  have hd : (gapPolynomial a b c 1 1).derivative.eval x.re=0 := by
    apply Complex.ofReal_injective
    simpa only [← gapPolynomial_derivative_eval_cast,Complex.ofReal_one,Complex.ofReal_zero] using hderiv
  exact positive_quintic_real_simple a b c x.re ha hb hc hr hd

end CentralConfigurations.FiveBody.D2.Resonance
