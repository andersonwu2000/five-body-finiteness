import CentralConfigurations.Algebra.PolynomialImage
import CentralConfigurations.Model.PotentialFiniteness
import CentralConfigurations.Model.SourceCoordinates
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Data.Fintype.Pi

/-!
# Algebraic finiteness and unbounded sequences

Lemma 2.1 implies that a bounded polynomial image is finite. Applying
this to all coordinates proves that a bounded affine algebraic set is
finite. The gauged central-configuration equations are such a set.
-/

namespace CentralConfigurations

noncomputable section

theorem finite_polynomial_image_of_bounded {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ ℂ)) (p : MvPolynomial σ ℂ)
    (h : ∃ C : ℝ, ∀ x ∈ MvPolynomial.zeroLocus ℂ I, ‖MvPolynomial.aeval x p‖ ≤ C) :
    ((fun x => MvPolynomial.aeval x p) '' MvPolynomial.zeroLocus ℂ I).Finite := by
  classical
  rcases polynomial_image_finite_or_cofinite I p with hf | hc
  · exact hf
  · exfalso
    obtain ⟨C, hC⟩ := h
    obtain ⟨B, hB⟩ := hc.isBounded.exists_norm_le
    obtain ⟨a, ha⟩ := NormedField.exists_lt_norm ℂ (max C B)
    by_cases hm : a ∈ (fun x => MvPolynomial.aeval x p) '' MvPolynomial.zeroLocus ℂ I
    · obtain ⟨x, hx, rfl⟩ := hm
      exact not_lt_of_ge ((hC x hx).trans (le_max_left C B)) ha
    · exact not_lt_of_ge ((hB a hm).trans (le_max_right C B)) ha

theorem finite_zeroLocus_of_coordinate_bounds {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ ℂ))
    (h : ∀ i : σ, ∃ C : ℝ, ∀ x ∈ MvPolynomial.zeroLocus ℂ I, ‖x i‖ ≤ C) :
    (MvPolynomial.zeroLocus ℂ I).Finite := by
  apply Set.forall_finite_image_eval_iff.mp
  intro i
  have hi := finite_polynomial_image_of_bounded I (MvPolynomial.X i) (by simpa using h i)
  simpa using hi

/-- The inverse distance is recovered polynomially from the two source
vectors. This avoids choosing any complex root when bounding delta. -/
theorem ZWSystem.delta_eq_zForce_mul_wSeparation {K : Type*} [CommRing K]
    {n : ℕ} {mass : Fin n → K} (q : ZWSystem K n mass) (i j : Fin n) :
    q.delta i j = q.zForce i j * (q.w i - q.w j) := by
  by_cases hij : i = j
  · subst j
    simp [q.delta_diagonal]
  · calc
      q.delta i j = q.delta i j *
          (q.delta i j ^ 2 * ((q.z i - q.z j) * (q.w i - q.w j))) := by
            rw [q.distance i j hij, mul_one]
      _ = _ := by unfold ZWSystem.zForce; ring

theorem NormalizedSystem.coordinate_norm_le_of_source_bound {n : ℕ} {mass : Fin n → ℂ}
    (q : NormalizedSystem ℂ n mass) {B : ℝ} (hB : 0 ≤ B)
    (hq : max ‖q.toZW.zSourceVector‖ ‖q.toZW.wSourceVector‖ ≤ B)
    (c : PolynomialEncoding.Coordinate n) :
    ‖PolynomialEncoding.assignment q c‖ ≤ B + 2 * B ^ 2 := by
  have hzv : ‖q.toZW.zVector‖ ≤ B := by
    rw [ZWSystem.zVector_norm_eq_source]
    exact (le_max_left _ _).trans hq
  have hwv : ‖q.toZW.wVector‖ ≤ B := by
    rw [ZWSystem.wVector_norm_eq_source]
    exact (le_max_right _ _).trans hq
  have hz (i : Fin n) : ‖q.toZW.z i‖ ≤ B := (q.toZW.norm_z_le i).trans hzv
  have hw (i : Fin n) : ‖q.toZW.w i‖ ≤ B := (q.toZW.swap.norm_z_le i).trans hwv
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  have hx (i : Fin n) : ‖q.x i‖ ≤ B := by
    have h : ‖q.toZW.toNormalized.x i‖ ≤ B := by
      change ‖(q.toZW.z i + q.toZW.w i) / 2‖ ≤ B
      rw [norm_div, htwo]
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      linarith [norm_add_le (q.toZW.z i) (q.toZW.w i), hz i, hw i]
    simpa only [q.toZW_toNormalized_x i] using h
  have hy (i : Fin n) : ‖q.y i‖ ≤ B := by
    have h : ‖q.toZW.toNormalized.y i‖ ≤ B := by
      change ‖Complex.I * (q.toZW.w i - q.toZW.z i) / 2‖ ≤ B
      rw [norm_div, norm_mul, Complex.norm_I, one_mul, htwo]
      apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      linarith [norm_sub_le (q.toZW.w i) (q.toZW.z i), hz i, hw i]
    simpa only [q.toZW_toNormalized_y i] using h
  have hd (i j : Fin n) : ‖q.delta i j‖ ≤ 2 * B ^ 2 := by
    change ‖q.toZW.delta i j‖ ≤ _
    rw [q.toZW.delta_eq_zForce_mul_wSeparation, norm_mul]
    have hf : ‖q.toZW.zForce i j‖ ≤ B := (q.toZW.norm_zForce_le i j).trans hzv
    have hs : ‖q.toZW.w i - q.toZW.w j‖ ≤ 2 * B := by
      linarith [norm_sub_le (q.toZW.w i) (q.toZW.w j), hw i, hw j]
    have hm := mul_le_mul hf hs (norm_nonneg _) hB
    nlinarith
  rcases c with i | (i | ⟨i, j⟩)
  · exact (hx i).trans (by nlinarith [sq_nonneg B])
  · exact (hy i).trans (by nlinarith [sq_nonneg B])
  · exact (hd i j).trans (by linarith)

namespace PolynomialEncoding

def gaugedIdeal {n : ℕ} (mass : Fin n → ℂ) (i j : Fin n) :
    Ideal (MvPolynomial (Coordinate n) ℂ) :=
  solutionIdeal mass ⊔ Ideal.span {MvPolynomial.X (yCoord i) - MvPolynomial.X (yCoord j)}

theorem mem_gauged_zeroLocus_iff {n : ℕ} (mass : Fin n → ℂ) (i j : Fin n)
    (a : Coordinate n → ℂ) :
    a ∈ MvPolynomial.zeroLocus ℂ (gaugedIdeal mass i j) ↔
      (∀ e, MvPolynomial.eval a (equations mass e) = 0) ∧ a (yCoord i) = a (yCoord j) := by
  change (gaugedIdeal mass i j ≤ RingHom.ker (MvPolynomial.aeval a)) ↔ _
  simp [gaugedIdeal, solutionIdeal, sup_le_iff, Ideal.span_le,
    Set.range_subset_iff, Set.singleton_subset_iff, RingHom.mem_ker, sub_eq_zero]

end PolynomialEncoding

theorem finite_gauged_systems_of_source_bounded {n : ℕ} (mass : Fin n → ℂ)
    (i j : Fin n) (hij : i ≠ j)
    (h : ∃ B : ℝ, ∀ q : NormalizedSystem ℂ n mass, q.InGauge i j →
      max ‖q.toZW.zSourceVector‖ ‖q.toZW.wSourceVector‖ ≤ B) :
    {q : NormalizedSystem ℂ n mass | q.InGauge i j}.Finite := by
  classical
  obtain ⟨B, hB⟩ := h
  have hf : (MvPolynomial.zeroLocus ℂ (PolynomialEncoding.gaugedIdeal mass i j)).Finite := by
    apply finite_zeroLocus_of_coordinate_bounds
    intro c
    refine ⟨max B 0 + 2 * (max B 0) ^ 2, ?_⟩
    intro a ha
    obtain ⟨ha, hg⟩ := (PolynomialEncoding.mem_gauged_zeroLocus_iff mass i j a).mp ha
    let q := PolynomialEncoding.ofCommonZero mass a ha
    have hq : q.InGauge i j := ⟨hij, hg⟩
    have hbq := q.coordinate_norm_le_of_source_bound (le_max_right B 0)
      ((hB q hq).trans (le_max_left B 0)) c
    simpa only [q, PolynomialEncoding.assignment_ofCommonZero] using hbq
  have hi : Function.Injective (PolynomialEncoding.assignment (mass := mass)) := by
    intro q q' he
    apply (PolynomialEncoding.commonZeroEquiv mass).injective
    exact Subtype.ext he
  apply (Set.finite_image_iff hi.injOn).mp
  apply hf.subset
  rintro a ⟨q, hq, rfl⟩
  apply (PolynomialEncoding.mem_gauged_zeroLocus_iff mass i j _).mpr
  exact ⟨PolynomialEncoding.normalized_vanishes q, hq.2⟩

/-- Infinite gauged solution sets supply the unbounded input required by
the singular-sequence extraction. This is a conclusion, not an input
assumption about a previously chosen sequence. -/
theorem exists_unbounded_gauged_sequence_of_infinite {n : ℕ} (mass : Fin n → ℂ)
    (i j : Fin n) (hij : i ≠ j)
    (hI : {q : NormalizedSystem ℂ n mass | q.InGauge i j}.Infinite) :
    ∃ q : ℕ → NormalizedSystem ℂ n mass, (∀ t, (q t).InGauge i j) ∧
      ¬ BddAbove (Set.range
        (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖)) := by
  classical
  have hlarge (B : ℝ) : ∃ q : NormalizedSystem ℂ n mass,
      q.InGauge i j ∧ B < max ‖q.toZW.zSourceVector‖ ‖q.toZW.wSourceVector‖ := by
    by_contra h
    push Not at h
    exact hI (finite_gauged_systems_of_source_bounded mass i j hij ⟨B, h⟩)
  choose q hq using fun t : ℕ => hlarge (t : ℝ)
  refine ⟨q, fun t => (hq t).1, ?_⟩
  rintro ⟨B, hB⟩
  obtain ⟨t, ht⟩ := exists_nat_gt B
  have hb := hB (Set.mem_range_self t)
  have hqt := (hq t).2
  linarith

end
end CentralConfigurations
