import CentralConfigurations.Asymptotics.FiniteDistanceData

/-!
# A distance that escapes along actual gauged solutions

The Section 9.1 use of a dominant polynomial is constructive at the level
of existence: infinitude of actual gauged solutions forces an infinite
distance-polynomial image, hence an unbounded image by Lemma 2.1. Choosing
successive large values gives a sequence whose same distance tends to
infinity. No initial singular sequence or divergent distance is assumed.
-/

namespace CentralConfigurations
noncomputable section
open scoped Topology
open Filter

namespace PolynomialEncoding

def squaredDistancePolynomial {n : ℕ} (a b : Fin n) :
    MvPolynomial (Coordinate n) ℂ :=
  (MvPolynomial.X (xCoord a) - MvPolynomial.X (xCoord b)) ^ 2 +
    (MvPolynomial.X (yCoord a) - MvPolynomial.X (yCoord b)) ^ 2

theorem squared_distance_polynomial_eval {n : ℕ}
    (a b : Fin n) (x : Coordinate n → ℂ) :
    MvPolynomial.aeval x (squaredDistancePolynomial a b) =
      squaredSeparation (fun i => x (xCoord i)) (fun i => x (yCoord i)) a b := by
  simp [squaredDistancePolynomial, squaredSeparation]

end PolynomialEncoding

theorem exists_infinite_distance_image_of_infinite_gauged {n : ℕ} (mass : Fin n → ℂ)
    (i j : Fin n) (hI : {q : NormalizedSystem ℂ n mass | q.InGauge i j}.Infinite) :
    ∃ a b : Fin n, a ≠ b ∧
      (Set.range (fun q : {q : NormalizedSystem ℂ n mass | q.InGauge i j} =>
        squaredSeparation q.val.x q.val.y a b)).Infinite := by
  classical
  have hh : ¬ ∀ a b, (Set.range (fun q : {q : NormalizedSystem ℂ n mass | q.InGauge i j} =>
      squaredSeparation q.val.x q.val.y a b)).Finite :=
    fun h => hI (finite_gauged_systems_of_finite_distances mass i j h)
  push Not at hh
  obtain ⟨a, b, hab⟩ := hh
  refine ⟨a, b, ?_, hab⟩
  intro he
  subst b
  apply hab
  simpa only [squaredSeparation, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero] using
    (Set.finite_range_const : (Set.range (fun _ :
      {q : NormalizedSystem ℂ n mass | q.InGauge i j} => (0 : ℂ))).Finite)

theorem exists_large_gauged_distance_of_infinite_image {n : ℕ} (mass : Fin n → ℂ)
    (i j : Fin n) (hij : i ≠ j) (a b : Fin n)
    (hI : (Set.range (fun q : {q : NormalizedSystem ℂ n mass | q.InGauge i j} =>
      squaredSeparation q.val.x q.val.y a b)).Infinite) (B : ℝ) :
    ∃ q : NormalizedSystem ℂ n mass, q.InGauge i j ∧ B < ‖squaredSeparation q.x q.y a b‖ := by
  classical
  by_contra hn
  push Not at hn
  have hf := finite_polynomial_image_of_bounded (PolynomialEncoding.gaugedIdeal mass i j)
    (PolynomialEncoding.squaredDistancePolynomial a b) (by
      refine ⟨B, ?_⟩
      intro x hx
      obtain ⟨he, hg⟩ := (PolynomialEncoding.mem_gauged_zeroLocus_iff mass i j x).mp hx
      let q := PolynomialEncoding.ofCommonZero mass x he
      have hq : q.InGauge i j := ⟨hij, hg⟩
      simpa only [PolynomialEncoding.squared_distance_polynomial_eval] using hn q hq)
  apply hI
  apply hf.subset
  rintro _ ⟨q, rfl⟩
  refine ⟨PolynomialEncoding.assignment q.val, ?_, ?_⟩
  · exact (PolynomialEncoding.mem_gauged_zeroLocus_iff mass i j _).mpr
      ⟨PolynomialEncoding.normalized_vanishes q.val, q.property.2⟩
  · simp [PolynomialEncoding.squared_distance_polynomial_eval,
      PolynomialEncoding.assignment, PolynomialEncoding.xCoord, PolynomialEncoding.yCoord]

theorem NormalizedSystem.squared_distance_norm_le_source_bound {n : ℕ} {mass : Fin n → ℂ}
    (q : NormalizedSystem ℂ n mass) {B : ℝ} (hB : 0 ≤ B)
    (hq : max ‖q.toZW.zSourceVector‖ ‖q.toZW.wSourceVector‖ ≤ B) (a b : Fin n) :
    ‖squaredSeparation q.x q.y a b‖ ≤ 4 * B ^ 2 := by
  have hz (k) : ‖q.toZW.z k‖ ≤ B := (q.toZW.norm_z_le k).trans (by
    rw [ZWSystem.zVector_norm_eq_source]
    exact (le_max_left _ _).trans hq)
  have hw (k) : ‖q.toZW.w k‖ ≤ B := (q.toZW.swap.norm_z_le k).trans (by
    change ‖q.toZW.wVector‖ ≤ B
    rw [ZWSystem.wVector_norm_eq_source]
    exact (le_max_right _ _).trans hq)
  have hz' : ‖q.toZW.z a - q.toZW.z b‖ ≤ 2 * B := by
    linarith [norm_sub_le (q.toZW.z a) (q.toZW.z b), hz a, hz b]
  have hw' : ‖q.toZW.w a - q.toZW.w b‖ ≤ 2 * B := by
    linarith [norm_sub_le (q.toZW.w a) (q.toZW.w b), hw a, hw b]
  rw [squaredSeparation, ← zw_separation_identity]
  change ‖(q.toZW.z a - q.toZW.z b) * (q.toZW.w a - q.toZW.w b)‖ ≤ _
  rw [norm_mul]
  nlinarith [mul_le_mul hz' hw' (norm_nonneg _) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hB)]

theorem exists_escaping_distance_sequence_of_infinite_gauged {n : ℕ} (mass : Fin n → ℂ)
    (i j : Fin n) (hij : i ≠ j)
    (hI : {q : NormalizedSystem ℂ n mass | q.InGauge i j}.Infinite) :
    ∃ a b : Fin n, a ≠ b ∧ ∃ q : ℕ → NormalizedSystem ℂ n mass,
      (∀ t, (q t).InGauge i j) ∧
      Tendsto (fun t => ‖squaredSeparation (q t).x (q t).y a b‖) atTop atTop ∧
      ¬ BddAbove (Set.range
        (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖)) := by
  classical
  obtain ⟨a, b, hab, hd⟩ := exists_infinite_distance_image_of_infinite_gauged mass i j hI
  choose q hq using fun t : ℕ =>
    exists_large_gauged_distance_of_infinite_image mass i j hij a b hd (t : ℝ)
  refine ⟨a, b, hab, q, fun t => (hq t).1, ?_, ?_⟩
  · exact tendsto_atTop_mono (fun t => (hq t).2.le) tendsto_natCast_atTop_atTop
  · rintro ⟨B, hB⟩
    obtain ⟨t, ht⟩ := exists_nat_gt (4 * (max B 0) ^ 2)
    have hbd := (q t).squared_distance_norm_le_source_bound (le_max_right B 0)
      ((hB (Set.mem_range_self t)).trans (le_max_left B 0)) a b
    exact (not_lt_of_ge hbd) (ht.trans (hq t).2)

end
end CentralConfigurations
