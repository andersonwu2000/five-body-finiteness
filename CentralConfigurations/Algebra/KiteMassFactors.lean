import CentralConfigurations.Algebra.TriangleMass

/-!
# The source factors in the kite mass relation

Chang (2023), Sections 9.3 and 11.1, equation (11.1), and Appendix IV,
printed p.160 / PDF p.165. The formulas were checked against the source page.
-/

namespace CentralConfigurations

def kiteMu6 {R : Type*} [CommRing R] (a b c : R) : R :=
  (a * b) ^ 3 - c ^ 2 * (a + b) ^ 4

def kiteMu15 {R : Type*} [CommRing R] (a b c : R) : R :=
  a ^ 6 * b ^ 6 - 2 * a ^ 7 * b ^ 3 * c ^ 2 + a ^ 6 * b ^ 4 * c ^ 2 +
    6 * a ^ 5 * b ^ 5 * c ^ 2 + a ^ 4 * b ^ 6 * c ^ 2 - 2 * a ^ 3 * b ^ 7 * c ^ 2 +
    a ^ 8 * c ^ 4 - a ^ 7 * b * c ^ 4 + a ^ 6 * b ^ 2 * c ^ 4 +
    2 * a ^ 5 * b ^ 3 * c ^ 4 - 2 * a ^ 4 * b ^ 4 * c ^ 4 +
    2 * a ^ 3 * b ^ 5 * c ^ 4 + a ^ 2 * b ^ 6 * c ^ 4 - a * b ^ 7 * c ^ 4 + b ^ 8 * c ^ 4

def kiteMu21 {R : Type*} [CommRing R] (a b c : R) : R :=
  -a ^ 11 * b ^ 2 + a ^ 11 * c ^ 2 + 4 * a ^ 9 * b ^ 2 * c ^ 2 +
    3 * a ^ 8 * b ^ 3 * c ^ 2 + 31 * a ^ 9 * c ^ 4 + 31 * a ^ 8 * b * c ^ 4 -
    6 * a ^ 7 * b ^ 2 * c ^ 4 - 9 * a ^ 6 * b ^ 3 * c ^ 4 - 3 * a ^ 5 * b ^ 4 * c ^ 4 +
    31 * a ^ 7 * c ^ 6 + 62 * a ^ 6 * b * c ^ 6 + 35 * a ^ 5 * b ^ 2 * c ^ 6 +
    9 * a ^ 4 * b ^ 3 * c ^ 6 + 6 * a ^ 3 * b ^ 4 * c ^ 6 + a ^ 2 * b ^ 5 * c ^ 6 +
    a ^ 5 * c ^ 8 + 3 * a ^ 4 * b * c ^ 8 + 2 * a ^ 3 * b ^ 2 * c ^ 8 -
    2 * a ^ 2 * b ^ 3 * c ^ 8 - 3 * a * b ^ 4 * c ^ 8 - b ^ 5 * c ^ 8

def kiteMu33 {R : Type*} [CommRing R] (a b c : R) : R :=
  3 * a ^ 12 * b ^ 4 + 9 * a ^ 11 * b ^ 5 - 24 * a ^ 12 * b ^ 2 * c ^ 2 -
    30 * a ^ 11 * b ^ 3 * c ^ 2 - 12 * a ^ 10 * b ^ 4 * c ^ 2 -
    30 * a ^ 9 * b ^ 5 * c ^ 2 - 28 * a ^ 8 * b ^ 6 * c ^ 2 +
    21 * a ^ 12 * c ^ 4 + 21 * a ^ 11 * b * c ^ 4 - 360 * a ^ 10 * b ^ 2 * c ^ 4 -
    670 * a ^ 9 * b ^ 3 * c ^ 4 - 292 * a ^ 8 * b ^ 4 * c ^ 4 +
    36 * a ^ 7 * b ^ 5 * c ^ 4 + 47 * a ^ 6 * b ^ 6 * c ^ 4 +
    29 * a ^ 5 * b ^ 7 * c ^ 4 - 154 * a ^ 10 * c ^ 6 - 308 * a ^ 9 * b * c ^ 6 -
    514 * a ^ 8 * b ^ 2 * c ^ 6 - 770 * a ^ 7 * b ^ 3 * c ^ 6 -
    472 * a ^ 6 * b ^ 4 * c ^ 6 - 68 * a ^ 5 * b ^ 5 * c ^ 6 -
    10 * a ^ 4 * b ^ 6 * c ^ 6 - 14 * a ^ 3 * b ^ 7 * c ^ 6 - 10 * a ^ 2 * b ^ 8 * c ^ 6 +
    21 * a ^ 8 * c ^ 8 + 63 * a ^ 7 * b * c ^ 8 + 39 * a ^ 6 * b ^ 2 * c ^ 8 -
    45 * a ^ 5 * b ^ 3 * c ^ 8 - 51 * a ^ 4 * b ^ 4 * c ^ 8 -
    3 * a ^ 3 * b ^ 5 * c ^ 8 - 3 * a ^ 2 * b ^ 6 * c ^ 8 - 15 * a * b ^ 7 * c ^ 8 -
    6 * b ^ 8 * c ^ 8

def kiteMassPolynomial {R : Type*} [CommRing R] (a b c : R) : R :=
  triangleMassPolynomial a b c * kiteMu6 a b c * kiteMu15 a b c

def kitePositiveQuartic {R : Type*} [CommRing R] (a b c : R) : R :=
  a ^ 2 * (b - c) ^ 2 + 2 * a * b * c * (b + c) + b ^ 2 * c ^ 2

noncomputable def kiteSourceMassRelation (a b c : ℝ) : ℝ :=
  (a ^ 3 - a * c ^ 2 - b * c ^ 2) * triangleMu5 a b c * kiteMu6 a b c *
    kiteMu15 a b c * kiteMu21 a b c * kiteMu33 a b c

theorem kite_positive_quartic_pos (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 < kitePositiveQuartic a b c := by
  dsimp [kitePositiveQuartic]
  positivity

theorem kite_source_mass_relation_of_polynomial (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : kiteMassPolynomial a b c = 0) :
    kiteSourceMassRelation a b c = 0 := by
  rcases mul_eq_zero.mp h with h | h
  · rcases mul_eq_zero.mp h with ht | hk
    · have he := triangle_mu5_eq_zero_of_polynomial a b c ha hb hc ht
      simp [kiteSourceMassRelation, he]
    · simp [kiteSourceMassRelation, hk]
  · simp [kiteSourceMassRelation, h]

end CentralConfigurations
