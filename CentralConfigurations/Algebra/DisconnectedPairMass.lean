import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The positive-mass elimination in Chang, Section 9.4

The squared cross-distance ratios retain every complex square-root branch.
Real and imaginary parts of the wedge equation force two cubic identities,
and positivity then gives the two equal-mass pairs (9.4).
-/

namespace CentralConfigurations

theorem complex_square_negative_real {z : ℂ} {r : ℝ} (hr : 0 < r)
    (h : z ^ 2 = ((-r : ℝ) : ℂ)) : z.re = 0 ∧ z.im ^ 2 = r := by
  have hR := congrArg Complex.re h
  have hI := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im] at hR hI
  have hp : z.re * z.im = 0 := by nlinarith [hI]
  have hz : z.re = 0 := by
    rcases mul_eq_zero.mp hp with h | h
    · exact h
    · rw [h] at hR
      nlinarith [sq_nonneg z.re]
  exact ⟨hz, by rw [hz] at hR; nlinarith [hR]⟩

theorem complex_square_positive_real {z : ℂ} {r : ℝ} (hr : 0 < r)
    (h : z ^ 2 = (r : ℂ)) : z.im = 0 ∧ z.re ^ 2 = r := by
  have hR := congrArg Complex.re h
  have hI := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im] at hR hI
  have hp : z.re * z.im = 0 := by nlinarith [hI]
  have hz : z.im = 0 := by
    rcases mul_eq_zero.mp hp with h | h
    · rw [h] at hR
      nlinarith [sq_nonneg z.im]
    · exact h
  exact ⟨hz, by rw [hz] at hR; nlinarith [hR]⟩

theorem disconnected_pair_mass_equalities (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (α β γ : ℂ)
    (hα : α ^ 2 = ((-(b / a) : ℝ) : ℂ))
    (hβ : β ^ 2 = ((-(d / c) : ℝ) : ℂ))
    (hγ : γ ^ 2 = ((b * d / (a * c) : ℝ) : ℂ))
    (ht : (c : ℂ) * a + c * b * α + d * a * β + d * b * γ = 0) :
    a = b ∧ c = d := by
  obtain ⟨hαR, hαI⟩ := complex_square_negative_real (div_pos hb ha) hα
  obtain ⟨hβR, hβI⟩ := complex_square_negative_real (div_pos hd hc) hβ
  obtain ⟨hγI, hγR⟩ := complex_square_positive_real
    (div_pos (mul_pos hb hd) (mul_pos ha hc)) hγ
  have hA : a * α.im ^ 2 = b := by rw [hαI]; field_simp
  have hB : c * β.im ^ 2 = d := by rw [hβI]; field_simp
  have hC : (a * c) * γ.re ^ 2 = b * d := by
    rw [hγR]; field_simp
  have hR := congrArg Complex.re ht
  have hI := congrArg Complex.im ht
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.zero_re, Complex.zero_im,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, hαR, hβR, hγI] at hR hI
  have hcube1 : (a * c) ^ 3 = (b * d) ^ 3 := by
    linear_combination (a*c)*(a*c-b*d*γ.re)*hR + (b*d)^2*hC
  have hcube2 : (b * c) ^ 3 = (a * d) ^ 3 := by
    linear_combination (a*c)*(b*c*α.im-a*d*β.im)*hI -
      c*(b*c)^2*hA + a*(a*d)^2*hB
  have hp1 : a*c = b*d := (show Odd 3 by decide).pow_injective hcube1
  have hp2 : b*c = a*d := (show Odd 3 by decide).pow_injective hcube2
  have hs : d * (a^2-b^2) = 0 := by
    linear_combination b*hp1 - a*hp2
  have hs2 : a^2 = b^2 := sub_eq_zero.mp ((mul_eq_zero.mp hs).resolve_left (ne_of_gt hd))
  have hab : a = b := by nlinarith [sq_nonneg (a-b)]
  refine ⟨hab, ?_⟩
  rw [hab] at hp1
  exact mul_left_cancel₀ (ne_of_gt hb) hp1

end CentralConfigurations
