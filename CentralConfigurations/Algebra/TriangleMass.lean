import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-!
# The positive-mass factors in Sections 9.2 and 11.1

The polynomial below is the square-root-free form of the source's three
possible inverse-square-root resonances. The complex fourth-power lemma
keeps all branches until positivity justifies real square roots.
-/

namespace CentralConfigurations

def triangleMassPolynomial {R : Type*} [CommRing R] (a b c : R) : R :=
  a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2 - 2 * a * b * c * (a + b + c)

theorem fourth_power_square_alternatives (z : ℂ) (p : ℝ)
    (h : z ^ 4 = (p : ℂ) ^ 2) : z ^ 2 = p ∨ z ^ 2 = -(p : ℂ) := by
  apply sq_eq_sq_iff_eq_or_eq_neg.mp
  convert h using 1
  ring

theorem fourth_power_real_axes (z : ℂ) (p : ℝ)
    (h : z ^ 4 = (p : ℂ) ^ 2) : z.re = 0 ∨ z.im = 0 := by
  have hp : z.re * z.im = 0 := by
    rcases fourth_power_square_alternatives z p h with hs | hs
    · have hi := congrArg Complex.im hs
      simp [pow_two, Complex.mul_im] at hi
      nlinarith
    · have hi := congrArg Complex.im hs
      simp [pow_two, Complex.mul_im] at hi
      nlinarith
  exact mul_eq_zero.mp hp

theorem fourth_power_sum_real (x y : ℂ) (p q : ℝ)
    (hx : x ^ 4 = (p : ℂ) ^ 2) (hy : y ^ 4 = (q : ℂ) ^ 2)
    (hs : x + y = -1) : x.im = 0 ∧ y.im = 0 := by
  have hr := congrArg Complex.re hs
  have hi := congrArg Complex.im hs
  simp only [Complex.add_re, Complex.neg_re, Complex.one_re] at hr
  simp only [Complex.add_im, Complex.neg_im, Complex.one_im, neg_zero] at hi
  rcases fourth_power_real_axes x p hx with hxr | hxi
  · rcases fourth_power_real_axes y q hy with hyr | hyi
    · simp [hxr, hyr] at hr
    · exact ⟨by linarith, hyi⟩
  · exact ⟨hxi, by linarith⟩

theorem real_square_of_fourth_power (z : ℂ) (p : ℝ) (hp : 0 < p)
    (hi : z.im = 0) (h : z ^ 4 = (p : ℂ) ^ 2) : z.re ^ 2 = p := by
  rcases fourth_power_square_alternatives z p h with hs | hs
  · have hr := congrArg Complex.re hs
    simpa [pow_two, Complex.mul_re, hi] using hr
  · have hr := congrArg Complex.re hs
    simp [pow_two, Complex.mul_re, hi] at hr
    nlinarith [sq_nonneg z.re]

theorem fourth_power_triangle_relation (x y : ℂ) (p q : ℝ)
    (hp : 0 < p) (hq : 0 < q)
    (hx : x ^ 4 = (p : ℂ) ^ 2) (hy : y ^ 4 = (q : ℂ) ^ 2)
    (hs : x + y = -1) :
    1 + p ^ 2 + q ^ 2 - 2 * (p + q + p * q) = 0 := by
  obtain ⟨hxi, hyi⟩ := fourth_power_sum_real x y p q hx hy hs
  have hxp := real_square_of_fourth_power x p hp hxi hx
  have hyq := real_square_of_fourth_power y q hq hyi hy
  have hr := congrArg Complex.re hs
  simp only [Complex.add_re, Complex.neg_re, Complex.one_re] at hr
  have hyr : y.re = -1 - x.re := by linarith
  rw [← hxp, ← hyq, hyr]
  ring

theorem triangle_mass_polynomial_of_roots (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (x y : ℂ)
    (hx : x ^ 4 = (-(b : ℂ) / (c : ℂ)) ^ 2)
    (hy : y ^ 4 = ((a : ℂ) / (c : ℂ)) ^ 2)
    (hs : x / (-(b : ℂ) / (c : ℂ)) = 1 + y / ((a : ℂ) / (c : ℂ))) :
    triangleMassPolynomial a b c = 0 := by
  have han : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha)
  have hbn : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hb)
  have hcn : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hc)
  let r : ℂ := (c : ℂ) / (b : ℂ) * x
  let s : ℂ := (c : ℂ) / (a : ℂ) * y
  have hr : r ^ 4 = ((c / b : ℝ) : ℂ) ^ 2 := by
    dsimp [r]
    rw [mul_pow, hx]
    push_cast
    field_simp [hbn, hcn]
  have ht : s ^ 4 = ((c / a : ℝ) : ℂ) ^ 2 := by
    dsimp [s]
    rw [mul_pow, hy]
    push_cast
    field_simp [han, hcn]
  have her : x / (-(b : ℂ) / (c : ℂ)) = -r := by
    dsimp [r]
    field_simp [hbn, hcn]
  have hes : y / ((a : ℂ) / (c : ℂ)) = s := by
    dsimp [s]
    field_simp [han, hcn]
  rw [her, hes] at hs
  have hrs : r + s = -1 := by linear_combination -hs
  have h := fourth_power_triangle_relation r s (c / b) (c / a)
    (div_pos hc hb) (div_pos hc ha) hr ht hrs
  field_simp [ne_of_gt ha, ne_of_gt hb] at h
  dsimp [triangleMassPolynomial]
  linear_combination h

noncomputable def triangleMu1 (a b c : ℝ) : ℝ :=
  Real.sqrt a * Real.sqrt b - Real.sqrt b * Real.sqrt c + Real.sqrt c * Real.sqrt a

noncomputable def triangleMu2 (a b c : ℝ) : ℝ :=
  a * b + b * c + c * a - 2 * a * Real.sqrt b * Real.sqrt c

noncomputable def triangleMu3 (a b c : ℝ) : ℝ :=
  triangleMu1 a b c * triangleMu1 b c a * triangleMu1 c a b

noncomputable def triangleMu4 (a b c : ℝ) : ℝ :=
  triangleMu2 a b c * triangleMu2 b c a * triangleMu2 c a b

noncomputable def triangleMu5 (a b c : ℝ) : ℝ :=
  triangleMu3 a b c * triangleMu4 b c a

theorem triangle_mu2_pos (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < triangleMu2 a b c := by
  have he : triangleMu2 a b c = a * (Real.sqrt b - Real.sqrt c) ^ 2 + b * c := by
    calc
      _ = a * ((Real.sqrt b) ^ 2 - 2 * Real.sqrt b * Real.sqrt c +
          (Real.sqrt c) ^ 2) + b * c := by
        rw [Real.sq_sqrt hb.le, Real.sq_sqrt hc.le]
        dsimp [triangleMu2]
        ring
      _ = _ := by ring
  rw [he]
  exact add_pos_of_nonneg_of_pos (mul_nonneg ha.le (sq_nonneg _)) (mul_pos hb hc)

theorem triangle_mu4_pos (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < triangleMu4 a b c :=
  mul_pos (mul_pos (triangle_mu2_pos a b c ha hb hc)
    (triangle_mu2_pos b c a hb hc ha)) (triangle_mu2_pos c a b hc ha hb)

theorem triangle_mass_squares_factorization (u v w : ℝ) :
    triangleMassPolynomial (u ^ 2) (v ^ 2) (w ^ 2) =
      -(u * v + v * w + w * u) *
        ((u * v - v * w + w * u) * (v * w - w * u + u * v) *
          (w * u - u * v + v * w)) := by
  dsimp [triangleMassPolynomial]
  ring

theorem triangle_mass_polynomial_factorization (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    triangleMassPolynomial a b c =
      -(Real.sqrt a * Real.sqrt b + Real.sqrt b * Real.sqrt c + Real.sqrt c * Real.sqrt a) *
        triangleMu3 a b c := by
  simpa only [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sq_sqrt hc, triangleMu3, triangleMu1]
    using triangle_mass_squares_factorization (Real.sqrt a) (Real.sqrt b) (Real.sqrt c)

theorem triangle_mu3_eq_zero_of_polynomial (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : triangleMassPolynomial a b c = 0) : triangleMu3 a b c = 0 := by
  have hp : 0 < Real.sqrt a * Real.sqrt b + Real.sqrt b * Real.sqrt c +
      Real.sqrt c * Real.sqrt a := by positivity
  rw [triangle_mass_polynomial_factorization a b c ha.le hb.le hc.le] at h
  exact (mul_eq_zero.mp h).resolve_left (neg_ne_zero.mpr (ne_of_gt hp))

theorem triangle_mu5_eq_zero_of_polynomial (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : triangleMassPolynomial a b c = 0) : triangleMu5 a b c = 0 := by
  rw [triangleMu5, triangle_mu3_eq_zero_of_polynomial a b c ha hb hc h, zero_mul]

end CentralConfigurations
