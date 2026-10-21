import CentralConfigurations.Algebra.KiteMassFactors
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The literal radical factors reused in Section 11.8

Section 9.3 gives eleven factors: the six factors of (9.1), a positive-real
three-quarter-power factor, a cubic factor, and mu15, mu21, mu33. This file
connects the certified polynomial restriction to that actual real expression.
-/

namespace CentralConfigurations

noncomputable def trianglePrintedSixFactors (a b c : ℝ) : ℝ :=
  (Real.sqrt a * Real.sqrt b - Real.sqrt a * Real.sqrt c - Real.sqrt b * Real.sqrt c) *
  (Real.sqrt a * Real.sqrt b + Real.sqrt a * Real.sqrt c - Real.sqrt b * Real.sqrt c) *
  (Real.sqrt a * Real.sqrt b - Real.sqrt a * Real.sqrt c + Real.sqrt b * Real.sqrt c) *
  triangleMu2 a b c * triangleMu2 b c a * triangleMu2 c a b

noncomputable def kiteRadicalFactor (a b c : ℝ) : ℝ :=
  -a ^ (3 / 4 : ℝ) * b ^ (3 / 4 : ℝ) + a * Real.sqrt c + b * Real.sqrt c

noncomputable def kiteRadicalSourceMassRelation (a b c : ℝ) : ℝ :=
  trianglePrintedSixFactors a b c * kiteRadicalFactor a b c *
    (a ^ 3 - (a + b) * c ^ 2) * kiteMu15 a b c * kiteMu21 a b c * kiteMu33 a b c

theorem triangle_printed_six_factors_eq (a b c : ℝ) :
    trianglePrintedSixFactors a b c = -triangleMu5 a b c := by
  dsimp [trianglePrintedSixFactors, triangleMu5, triangleMu3, triangleMu4,
    triangleMu1, triangleMu2]
  ring

theorem rpow_three_quarters_fourth (a : ℝ) (ha : 0 ≤ a) :
    (a ^ (3 / 4 : ℝ)) ^ 4 = a ^ 3 := by
  calc
    _ = a ^ ((3 / 4 : ℝ) * (4 : ℕ)) := (Real.rpow_mul_natCast ha _ 4).symm
    _ = _ := by norm_num

theorem kite_radical_factor_zero_of_mu6 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : kiteMu6 a b c = 0) :
    kiteRadicalFactor a b c = 0 := by
  have hsqrt : (Real.sqrt c) ^ 4 = c ^ 2 := by
    calc
      _ = ((Real.sqrt c) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hc.le]
  have hp : (a ^ (3 / 4 : ℝ) * b ^ (3 / 4 : ℝ)) ^ 4 =
      ((a + b) * Real.sqrt c) ^ 4 := by
    rw [mul_pow, mul_pow, rpow_three_quarters_fourth a ha.le,
      rpow_three_quarters_fourth b hb.le, hsqrt]
    dsimp [kiteMu6] at h
    linear_combination h
  have he := (pow_left_inj₀
    (mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg hb.le _))
    (mul_nonneg (add_nonneg ha.le hb.le) (Real.sqrt_nonneg c))
    (by decide : (4 : ℕ) ≠ 0)).mp hp
  dsimp [kiteRadicalFactor]
  linear_combination -he

theorem kite_radical_source_relation_of_polynomial (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : kiteMassPolynomial a b c = 0) :
    kiteRadicalSourceMassRelation a b c = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with ht | hk
    · have he := triangle_mu5_eq_zero_of_polynomial a b c ha hb hc ht
      simp [kiteRadicalSourceMassRelation, triangle_printed_six_factors_eq, he]
    · have he := kite_radical_factor_zero_of_mu6 a b c ha hb hc hk
      simp [kiteRadicalSourceMassRelation, he]
  · simp [kiteRadicalSourceMassRelation, h]

end CentralConfigurations
