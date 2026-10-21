import CentralConfigurations.FiveBody.D2Resonance.GapPolynomial

noncomputable section
open Polynomial
namespace CentralConfigurations.FiveBody.D2.Resonance
set_option maxHeartbeats 2000000

def cubicDiscriminant {R : Type*} [CommRing R] (A B C D : R) : R :=
  B^2*C^2-4*A*C^3-4*B^3*D-27*A^2*D^2+18*A*B*C*D

theorem cubic_discriminant_certificate {R : Type*} [CommRing R]
    (A B C D x : R) :
    cubicDiscriminant A B C D =
      ((-27*A^2*D+15*A*B*C-4*B^3)+(18*A^2*C-6*A*B^2)*x)*
        (A*x^3+B*x^2+C*x+D) +
      ((3*A*B*D-4*A*C^2+B^2*C)+(9*A^2*D-7*A*B*C+2*B^3)*x+
        (-6*A^2*C+2*A*B^2)*x^2)*(3*A*x^2+2*B*x+C) := by
  dsimp [cubicDiscriminant]
  ring

theorem alternating_discriminant_expand {R : Type*} [CommRing R] (a b c : R) :
    cubicDiscriminant (a+b) (-a-2*b) (-a-2*c) (a+c) =
      32*a^3*b+32*a^3*c+61*a^2*b^2+118*a^2*b*c+61*a^2*c^2+
      32*a*b^3+118*a*b^2*c+118*a*b*c^2+32*a*c^3+32*b^3*c+
      61*b^2*c^2+32*b*c^3 := by
  dsimp [cubicDiscriminant]
  ring

theorem alternating_discriminant_pos (a b c : ℝ) (ha : 0<a) (hb : 0<b) (hc : 0<c) :
    0 < cubicDiscriminant (a+b) (-a-2*b) (-a-2*c) (a+c) := by
  rw [alternating_discriminant_expand]
  positivity

def alternatingCubic {R : Type*} [CommRing R] (a b c x : R) : R :=
  a*(x-1)^2*(x+1)+b*x^2*(x-2)+c*(1-2*x)

def alternatingCubicDerivative {R : Type*} [CommRing R] (a b c x : R) : R :=
  3*(a+b)*x^2+2*(-a-2*b)*x+(-a-2*c)

theorem alternating_cubic_expand {R : Type*} [CommRing R] (a b c x : R) :
    alternatingCubic a b c x =
      (a+b)*x^3+(-a-2*b)*x^2+(-a-2*c)*x+(a+c) := by
  dsimp [alternatingCubic]
  ring

theorem alternating_cubic_remainder {R : Type*} [CommRing R] (a b c x : R) :
    alternatingCubic a b c x =
      (x^2-x+1)*((a+b)*x-b)+(a+b+c)*(1-2*x) := by
  dsimp [alternatingCubic]
  ring

theorem alternating_cubic_simple (a b c : ℝ) (x : ℂ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hg : alternatingCubic (a:ℂ) (b:ℂ) (c:ℂ) x=0) :
    alternatingCubicDerivative (a:ℂ) (b:ℂ) (c:ℂ) x≠0 := by
  intro hd
  have hid := cubic_discriminant_certificate ((a:ℂ)+b) (-(a:ℂ)-2*b)
    (-(a:ℂ)-2*c) ((a:ℂ)+c) x
  rw [← alternating_cubic_expand] at hid
  change cubicDiscriminant ((a:ℂ)+b) (-(a:ℂ)-2*b) (-(a:ℂ)-2*c) ((a:ℂ)+c) = _ at hid
  change alternatingCubicDerivative (a:ℂ) (b:ℂ) (c:ℂ) x=0 at hd
  dsimp [alternatingCubicDerivative] at hd
  rw [hg,hd] at hid
  have hz : cubicDiscriminant (a+b) (-a-2*b) (-a-2*c) (a+c)=0 := by
    apply Complex.ofReal_injective
    simpa [cubicDiscriminant] using hid
  have := alternating_discriminant_pos a b c ha hb hc
  linarith

theorem quadratic_simple (x : ℂ) (hq : x^2-x+1=0) : 2*x-1≠0 := by
  intro h
  have hx : x=(1/2:ℂ) := by linear_combination h/2
  norm_num [hx] at hq

theorem alternating_cubic_quadratic_disjoint (a b c : ℝ) (x : ℂ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hq : x^2-x+1=0) :
    alternatingCubic (a:ℂ) (b:ℂ) (c:ℂ) x≠0 := by
  intro hg
  have hm : (a:ℂ)+b+c≠0 := by
    exact_mod_cast (ne_of_gt (by linarith : 0<a+b+c))
  have hid := alternating_cubic_remainder (a:ℂ) (b:ℂ) (c:ℂ) x
  rw [hq,hg] at hid
  have hx : 1-2*x=0 := (mul_eq_zero.mp (by simpa using hid.symm)).resolve_left hm
  exact quadratic_simple x hq (by linear_combination -hx)

theorem alternating_factor (a b c x : ℂ) :
    (gapPolynomial a b c (-1) 1).eval x =
      -(x^2-x+1)*alternatingCubic a b c x := by
  simp [gapPolynomial,alternatingCubic]
  ring

theorem alternating_derivative_factor (a b c x : ℂ) :
    (gapPolynomial a b c (-1) 1).derivative.eval x =
      -(2*x-1)*alternatingCubic a b c x-
        (x^2-x+1)*alternatingCubicDerivative a b c x := by
  simp [gapPolynomial,alternatingCubic,alternatingCubicDerivative,
    derivative_mul,derivative_pow]
  ring

theorem alternating_no_repeated_root (a b c : ℝ) (x : ℂ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hroot : (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) (-1) 1).eval x=0)
    (hderiv : (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) (-1) 1).derivative.eval x=0) : False := by
  rw [alternating_factor] at hroot
  rw [alternating_derivative_factor] at hderiv
  rcases mul_eq_zero.mp hroot with hq | hg
  · have hq' : x^2-x+1=0 := neg_eq_zero.mp hq
    rw [hq'] at hderiv
    have hgn := alternating_cubic_quadratic_disjoint a b c x ha hb hc hq'
    have hn := quadratic_simple x hq'
    have : -(2*x-1)*alternatingCubic (a:ℂ) (b:ℂ) (c:ℂ) x=0 := by simpa using hderiv
    exact (mul_ne_zero (neg_ne_zero.mpr hn) hgn) this
  · have hqn : x^2-x+1≠0 := by
      intro hq
      exact alternating_cubic_quadratic_disjoint a b c x ha hb hc hq hg
    rw [hg] at hderiv
    have : alternatingCubicDerivative (a:ℂ) (b:ℂ) (c:ℂ) x=0 := by
      apply (mul_eq_zero.mp (by simpa using hderiv)).resolve_left hqn
    exact alternating_cubic_simple a b c x ha hb hc hg this

end CentralConfigurations.FiveBody.D2.Resonance
