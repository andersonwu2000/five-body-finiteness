import CentralConfigurations.FiveBody.D2Resonance.Alternating
import CentralConfigurations.FiveBody.D2Resonance.PositiveFactor
import CentralConfigurations.FiveBody.D2Exceptional.GapSignTransport

noncomputable section
open Polynomial
namespace CentralConfigurations.FiveBody.D2.Resonance
open Exceptional
set_option maxHeartbeats 2000000

structure RepeatedGap (a b c : ℝ) (x s13 s23 : ℂ) : Prop where
  x_ne_zero : x≠0
  x_ne_one : x≠1
  euler_zero : gapEuler (a:ℂ) (b:ℂ) (c:ℂ) x s13 s23=0
  resonant : gapLambda (a:ℂ) (b:ℂ) (c:ℂ) x s13 s23-
    2*gapTrace (a:ℂ) (b:ℂ) (c:ℂ) x s13 s23=0

theorem RepeatedGap.polynomial_zeros {a b c : ℝ} {x s13 s23 : ℂ}
    (h : RepeatedGap a b c x s13 s23) :
    (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) s13 s23).eval x=0 ∧
    (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) s13 s23).derivative.eval x=0 := by
  constructor
  · rw [gapPolynomial_eval _ _ _ _ _ _ h.x_ne_zero h.x_ne_one,h.euler_zero,mul_zero]
  · rw [gapPolynomial_derivative_eval _ _ _ _ _ _ h.x_ne_zero h.x_ne_one,
      h.euler_zero,h.resonant]
    ring

theorem RepeatedGap.swap12 {a b c : ℝ} {x : ℂ}
    (h : RepeatedGap a b c x 1 (-1)) : RepeatedGap a c b (1/x) 1 1 := by
  have hy : 1/x≠0 := one_div_ne_zero h.x_ne_zero
  have hy1 : 1/x≠1 := by
    intro he
    have hx : x=1 := by
      have hh := (div_eq_iff h.x_ne_zero).mp he
      simpa using hh.symm
    exact h.x_ne_one hx
  have hi : 1/(1/x)=x := by field_simp
  obtain ⟨hE,hT,hL⟩ := gap_sign_swap12 (a:ℂ) (c:ℂ) (b:ℂ) (1/x) hy hy1
  rw [hi] at hE hT hL
  have he : gapEuler (a:ℂ) (c:ℂ) (b:ℂ) (1/x) 1 1=0 := by
    rw [h.euler_zero] at hE
    exact (mul_eq_zero.mp hE.symm).resolve_left (neg_ne_zero.mpr hy)
  have hs : gapLambda (a:ℂ) (c:ℂ) (b:ℂ) (1/x) 1 1-
      2*gapTrace (a:ℂ) (c:ℂ) (b:ℂ) (1/x) 1 1=0 := by
    rw [he,mul_zero,add_zero] at hL
    have hz : (1/x)^3*(gapLambda (a:ℂ) (c:ℂ) (b:ℂ) (1/x) 1 1-
        2*gapTrace (a:ℂ) (c:ℂ) (b:ℂ) (1/x) 1 1)=0 := by
      linear_combination h.resonant-hL+2*hT
    exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero 3 hy)
  exact ⟨hy,hy1,he,hs⟩

theorem RepeatedGap.swap01 {a b c : ℝ} {x : ℂ}
    (h : RepeatedGap a b c x (-1) (-1)) : RepeatedGap b a c (1-x) 1 1 := by
  have hy : 1-x≠0 := sub_ne_zero.mpr (Ne.symm h.x_ne_one)
  have hy1 : 1-x≠1 := by intro he; exact h.x_ne_zero (by linear_combination -he)
  have hi : 1-(1-x)=x := by ring
  obtain ⟨hE,hT,hL⟩ := gap_sign_swap01 (b:ℂ) (a:ℂ) (c:ℂ) (1-x) hy hy1
  rw [hi] at hE hT hL
  have he : gapEuler (b:ℂ) (a:ℂ) (c:ℂ) (1-x) 1 1=0 := by
    rw [h.euler_zero] at hE
    exact neg_eq_zero.mp hE.symm
  have hs : gapLambda (b:ℂ) (a:ℂ) (c:ℂ) (1-x) 1 1-
      2*gapTrace (b:ℂ) (a:ℂ) (c:ℂ) (1-x) 1 1=0 := by
    linear_combination h.resonant-hL+2*hT
  exact ⟨hy,hy1,he,hs⟩

theorem RepeatedGap.alternating_false {a b c : ℝ} {x : ℂ}
    (h : RepeatedGap a b c x (-1) 1) (ha : 0<a) (hb : 0<b) (hc : 0<c) : False := by
  obtain ⟨h0,h1⟩ := h.polynomial_zeros
  exact alternating_no_repeated_root a b c x ha hb hc h0 h1

end CentralConfigurations.FiveBody.D2.Resonance
