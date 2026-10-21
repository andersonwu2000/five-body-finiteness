import CentralConfigurations.Algebra.KiteRadicalSource
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# The source least common multiples in fourth-root coordinates

Sections 10.3 and 11.9--11.11 combine three choices of the two closed rows.
We realize the printed radical expressions as polynomials in the positive
fourth roots of the masses, and take polynomial least common multiples.
The resulting expression is characterized by the polynomial LCM property.
The choice of a unit normalization cannot affect the zero relation.
-/

namespace CentralConfigurations

noncomputable section

def rootTriangleMu2 {R : Type*} [CommRing R] (a b c : R) : R :=
  a ^ 4 * b ^ 4 + b ^ 4 * c ^ 4 + c ^ 4 * a ^ 4 - 2 * a ^ 4 * b ^ 2 * c ^ 2

def rootTriangleSixFactors {R : Type*} [CommRing R] (a b c : R) : R :=
  (a ^ 2 * b ^ 2 - a ^ 2 * c ^ 2 - b ^ 2 * c ^ 2) *
  (a ^ 2 * b ^ 2 + a ^ 2 * c ^ 2 - b ^ 2 * c ^ 2) *
  (a ^ 2 * b ^ 2 - a ^ 2 * c ^ 2 + b ^ 2 * c ^ 2) *
  rootTriangleMu2 a b c * rootTriangleMu2 b c a * rootTriangleMu2 c a b

def rootKiteElevenFactors {R : Type*} [CommRing R] (a b c : R) : R :=
  rootTriangleSixFactors a b c * (-a ^ 3 * b ^ 3 + a ^ 4 * c ^ 2 + b ^ 4 * c ^ 2) *
    ((a ^ 4) ^ 3 - (a ^ 4 + b ^ 4) * (c ^ 4) ^ 2) *
    kiteMu15 (a ^ 4) (b ^ 4) (c ^ 4) * kiteMu21 (a ^ 4) (b ^ 4) (c ^ 4) *
    kiteMu33 (a ^ 4) (b ^ 4) (c ^ 4)

theorem rpow_quarter_fourth (a : ℝ) (ha : 0 ≤ a) :
    (a ^ (1 / 4 : ℝ)) ^ 4 = a := by
  calc
    _ = a ^ ((1 / 4 : ℝ) * (4 : ℕ)) := (Real.rpow_mul_natCast ha _ 4).symm
    _ = _ := by norm_num

theorem rpow_quarter_square (a : ℝ) (ha : 0 ≤ a) :
    (a ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt a := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast ha]
  norm_num

theorem rpow_quarter_cube (a : ℝ) (ha : 0 ≤ a) :
    (a ^ (1 / 4 : ℝ)) ^ 3 = a ^ (3 / 4 : ℝ) := by
  rw [← Real.rpow_mul_natCast ha]
  norm_num

theorem root_kite_eleven_at_quarter (a b c : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    rootKiteElevenFactors (a ^ (1 / 4 : ℝ)) (b ^ (1 / 4 : ℝ)) (c ^ (1 / 4 : ℝ)) =
      kiteRadicalSourceMassRelation a b c := by
  simp only [rootKiteElevenFactors, rootTriangleSixFactors, rootTriangleMu2,
    rpow_quarter_fourth a ha, rpow_quarter_fourth b hb, rpow_quarter_fourth c hc,
    rpow_quarter_square a ha, rpow_quarter_square b hb, rpow_quarter_square c hc,
    rpow_quarter_cube a ha, rpow_quarter_cube b hb,
    kiteRadicalSourceMassRelation, trianglePrintedSixFactors, kiteRadicalFactor, triangleMu2]
theorem kite_mass_polynomial_swap_first {R : Type*} [CommRing R] (a b c : R) :
    kiteMassPolynomial a b c = kiteMassPolynomial b a c := by
  dsimp [kiteMassPolynomial, triangleMassPolynomial, kiteMu6, kiteMu15]
  ring

variable {n : ℕ}

local instance rootPolynomialGCD : GCDMonoid (MvPolynomial (Fin n) ℝ) :=
  UniqueFactorizationMonoid.toGCDMonoid _

def sourceKiteRootPolynomial (i j k : Fin n) : MvPolynomial (Fin n) ℝ :=
  rootKiteElevenFactors (MvPolynomial.X i) (MvPolynomial.X j) (MvPolynomial.X k)

def sourceTriangleRootPolynomial (i j k : Fin n) : MvPolynomial (Fin n) ℝ :=
  rootTriangleSixFactors (MvPolynomial.X i) (MvPolynomial.X j) (MvPolynomial.X k)

/-- The three canonical row pairs for the triangle (i,j,k). -/
def sourceTriangleKiteLCM (i j k : Fin n) : MvPolynomial (Fin n) ℝ :=
  lcm (sourceKiteRootPolynomial i j k)
    (lcm (sourceKiteRootPolynomial j k i) (sourceKiteRootPolynomial i k j))

def sourceTwoTriangleKiteLCM (i j k a b c : Fin n) : MvPolynomial (Fin n) ℝ :=
  lcm (sourceTriangleKiteLCM i j k) (sourceTriangleKiteLCM a b c)

theorem source_kite_root_polynomial_eval (v : Fin n → ℝ) (i j k : Fin n) :
    MvPolynomial.eval v (sourceKiteRootPolynomial i j k) =
      rootKiteElevenFactors (v i) (v j) (v k) := by
  simp [sourceKiteRootPolynomial, rootKiteElevenFactors, rootTriangleSixFactors,
    rootTriangleMu2, kiteMu15, kiteMu21, kiteMu33]

theorem eval_zero_of_polynomial_dvd (v : Fin n → ℝ) (P Q : MvPolynomial (Fin n) ℝ)
    (h : P ∣ Q) (hz : MvPolynomial.eval v P = 0) : MvPolynomial.eval v Q = 0 := by
  obtain ⟨R, rfl⟩ := h
  rw [map_mul, hz, zero_mul]

theorem source_kite_root_polynomial_ne_zero (i j k : Fin n) :
    sourceKiteRootPolynomial i j k ≠ 0 := by
  have hv : MvPolynomial.eval (fun _ => (1 : ℝ)) (sourceKiteRootPolynomial i j k) ≠ 0 := by
    rw [source_kite_root_polynomial_eval]
    norm_num [rootKiteElevenFactors, rootTriangleSixFactors, rootTriangleMu2,
      kiteMu15, kiteMu21, kiteMu33]
  intro he
  apply hv
  rw [he, map_zero]

theorem source_triangle_kite_lcm_ne_zero (i j k : Fin n) :
    sourceTriangleKiteLCM i j k ≠ 0 := by
  intro hz
  rcases (lcm_eq_zero_iff (sourceKiteRootPolynomial i j k)
    (lcm (sourceKiteRootPolynomial j k i) (sourceKiteRootPolynomial i k j))).mp hz with h | h
  · exact source_kite_root_polynomial_ne_zero i j k h
  · rcases (lcm_eq_zero_iff (sourceKiteRootPolynomial j k i) (sourceKiteRootPolynomial i k j)).mp h with h | h
    · exact source_kite_root_polynomial_ne_zero j k i h
    · exact source_kite_root_polynomial_ne_zero i k j h

theorem source_two_triangle_kite_lcm_ne_zero (i j k a b c : Fin n) :
    sourceTwoTriangleKiteLCM i j k a b c ≠ 0 := by
  intro hz
  rcases (lcm_eq_zero_iff (sourceTriangleKiteLCM i j k) (sourceTriangleKiteLCM a b c)).mp hz with h | h
  · exact source_triangle_kite_lcm_ne_zero i j k h
  · exact source_triangle_kite_lcm_ne_zero a b c h

theorem source_triangle_kite_lcm_eval_zero (mass : Fin n → ℝ)
    (hm : ∀ a, 0 < mass a) (i j k : Fin n)
    (h : kiteMassPolynomial (mass i) (mass j) (mass k) = 0 ∨
      kiteMassPolynomial (mass j) (mass k) (mass i) = 0 ∨
      kiteMassPolynomial (mass k) (mass i) (mass j) = 0) :
    MvPolynomial.eval (fun a => mass a ^ (1 / 4 : ℝ)) (sourceTriangleKiteLCM i j k) = 0 := by
  have he (a b c : Fin n) (hc : kiteMassPolynomial (mass a) (mass b) (mass c) = 0) :
      MvPolynomial.eval (fun a => mass a ^ (1 / 4 : ℝ)) (sourceKiteRootPolynomial a b c) = 0 := by
    rw [source_kite_root_polynomial_eval,
      root_kite_eleven_at_quarter _ _ _ (hm a).le (hm b).le (hm c).le]
    exact kite_radical_source_relation_of_polynomial _ _ _ (hm a) (hm b) (hm c) hc
  rcases h with h | h | h
  · exact eval_zero_of_polynomial_dvd _ _ _ (dvd_lcm_left _ _) (he i j k h)
  · exact eval_zero_of_polynomial_dvd _ _ _
      ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)) (he j k i h)
  · have hs : kiteMassPolynomial (mass i) (mass k) (mass j) = 0 := by
      rw [kite_mass_polynomial_swap_first]; exact h
    exact eval_zero_of_polynomial_dvd _ _ _
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)) (he i k j hs)

theorem source_two_triangle_kite_lcm_eval_zero_left (v : Fin n → ℝ)
    (i j k a b c : Fin n) (h : MvPolynomial.eval v (sourceTriangleKiteLCM i j k) = 0) :
    MvPolynomial.eval v (sourceTwoTriangleKiteLCM i j k a b c) = 0 :=
  eval_zero_of_polynomial_dvd _ _ _ (dvd_lcm_left _ _) h

/-- The six-factor branch from Section 9.2 is already a divisor of the
eleven-factor branch, so adding it does not impose an extra mass branch. -/
theorem root_triangle_six_dvd_kite_eleven {R : Type*} [CommRing R] (a b c : R) :
    rootTriangleSixFactors a b c ∣ rootKiteElevenFactors a b c := by
  dsimp [rootKiteElevenFactors]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_of_dvd_left
    (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _) _) _

/-- The source's earlier six-factor case and repeated eleven-factor case
do not alter the least common multiple of its three distinct pivot cases. -/
theorem source_triangle_kite_lcm_source_least (i j k : Fin n)
    (Q : MvPolynomial (Fin n) ℝ) :
    sourceTriangleKiteLCM i j k ∣ Q ↔
      sourceTriangleRootPolynomial j k i ∣ Q ∧
      sourceKiteRootPolynomial j k i ∣ Q ∧
      sourceKiteRootPolynomial i j k ∣ Q ∧ sourceKiteRootPolynomial i k j ∣ Q := by
  constructor
  · intro h
    have hfirst : sourceKiteRootPolynomial i j k ∣ Q :=
      (dvd_lcm_left _ _).trans h
    have hrest : lcm (sourceKiteRootPolynomial j k i) (sourceKiteRootPolynomial i k j) ∣ Q :=
      (dvd_lcm_right _ _).trans h
    have hsecond : sourceKiteRootPolynomial j k i ∣ Q := (dvd_lcm_left _ _).trans hrest
    have hthird : sourceKiteRootPolynomial i k j ∣ Q := (dvd_lcm_right _ _).trans hrest
    exact ⟨(root_triangle_six_dvd_kite_eleven (MvPolynomial.X j) (MvPolynomial.X k)
      (MvPolynomial.X i)).trans hsecond, hsecond, hfirst, hthird⟩
  · rintro ⟨_, hsecond, hfirst, hthird⟩
    exact lcm_dvd hfirst (lcm_dvd hsecond hthird)

theorem source_two_triangle_kite_lcm_least (i j k a b c : Fin n)
    (Q : MvPolynomial (Fin n) ℝ) :
    sourceTwoTriangleKiteLCM i j k a b c ∣ Q ↔
      sourceTriangleKiteLCM i j k ∣ Q ∧ sourceTriangleKiteLCM a b c ∣ Q :=
  lcm_dvd_iff

end
end CentralConfigurations
