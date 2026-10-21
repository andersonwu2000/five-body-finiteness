import CentralConfigurations.Asymptotics.FourProductAlgebra
import CentralConfigurations.Asymptotics.DominantDistances

/-!
# Selecting an escaping four-product on actual five-body solutions

The finite-fiber recovery identity and the proved polynomial-image theorem
provide the selection directly on the gauged solution set. No singular
sequence, escaping observable, or special mass restriction is assumed.
-/

namespace CentralConfigurations
noncomputable section
open scoped BigOperators Topology
open Filter

def fiveBodyDistanceData {R : Type*} [CommRing R] (x y : Fin 5 → R) (e : Fin 10) : R :=
  squaredSeparation x y (fiveBodyEdges e).1 (fiveBodyEdges e).2

theorem five_body_edge_coverage : ∀ a b : Fin 5, a ≠ b →
    ∃ e : Fin 10, fiveBodyEdges e = (a,b) ∨ fiveBodyEdges e = (b,a) := by decide +kernel

theorem five_body_distance_data_coverage (a b : Fin 5) (hab : a ≠ b) :
    ∃ e : Fin 10, ∀ x y : Fin 5 → ℂ,
      fiveBodyDistanceData x y e = squaredSeparation x y a b := by
  obtain ⟨e,he⟩ := five_body_edge_coverage a b hab
  refine ⟨e, fun x y => ?_⟩
  rcases he with he | he
  · simp only [fiveBodyDistanceData,he]
  · simp only [fiveBodyDistanceData,he,squaredSeparation]
    ring

def NormalizedSystem.fiveBodyFourProduct {mass : Fin 5 → ℂ}
    (q : NormalizedSystem ℂ 5 mass) (e : Fin 10) : ℂ :=
  fiveBodyFourProducts (fiveBodyDistanceData q.x q.y) e

theorem NormalizedSystem.five_body_four_product_ne_zero {mass : Fin 5 → ℂ}
    (q : NormalizedSystem ℂ 5 mass) (e : Fin 10) : q.fiveBodyFourProduct e ≠ 0 :=
  CentralConfigurations.five_body_four_product_ne_zero _
    (fun k => q.separation_ne_zero (five_body_edge_distinct k)) e

theorem finite_gauged_five_body_of_finite_four_products (mass : Fin 5 → ℂ) (i j : Fin 5)
    (h : ∀ e, (Set.range (fun q : {q : NormalizedSystem ℂ 5 mass | q.InGauge i j} =>
      q.val.fiveBodyFourProduct e)).Finite) :
    {q : NormalizedSystem ℂ 5 mass | q.InGauge i j}.Finite := by
  have hd := finite_distance_images_of_finite_four_product_images
    (fun q : {q : NormalizedSystem ℂ 5 mass | q.InGauge i j} =>
      fiveBodyDistanceData q.val.x q.val.y)
    (fun q e => q.val.separation_ne_zero (five_body_edge_distinct e)) h
  apply finite_gauged_systems_of_finite_distances
  intro a b
  by_cases hab : a = b
  · subst b
    simpa only [squaredSeparation,sub_self,zero_pow (by decide : 2 ≠ 0),add_zero] using
      (Set.finite_range_const : (Set.range (fun _ :
        {q : NormalizedSystem ℂ 5 mass | q.InGauge i j} => (0 : ℂ))).Finite)
  · obtain ⟨e,he⟩ := five_body_distance_data_coverage a b hab
    simpa only [he] using hd e

namespace PolynomialEncoding

def fiveBodyFourProductPolynomial (e : Fin 10) : MvPolynomial (Coordinate 5) ℂ :=
  fiveBodyFourProducts (fun k => squaredDistancePolynomial (fiveBodyEdges k).1
    (fiveBodyEdges k).2) e

theorem five_body_four_product_polynomial_eval (e : Fin 10) (x : Coordinate 5 → ℂ) :
    MvPolynomial.aeval x (fiveBodyFourProductPolynomial e) =
      fiveBodyFourProducts (fiveBodyDistanceData (fun k => x (xCoord k))
        (fun k => x (yCoord k))) e := by
  simp [fiveBodyFourProductPolynomial,fiveBodyFourProducts,fiveBodyDistanceData,
    squaredDistancePolynomial,squaredSeparation]

end PolynomialEncoding

theorem exists_infinite_four_product_image_of_infinite_gauged
    (mass : Fin 5 → ℂ) (i j : Fin 5)
    (hI : {q : NormalizedSystem ℂ 5 mass | q.InGauge i j}.Infinite) :
    ∃ e : Fin 10, (Set.range (fun q : {q : NormalizedSystem ℂ 5 mass | q.InGauge i j} =>
      q.val.fiveBodyFourProduct e)).Infinite := by
  by_contra hn
  push Not at hn
  exact hI (finite_gauged_five_body_of_finite_four_products mass i j hn)

theorem exists_large_gauged_four_product_of_infinite_image (mass : Fin 5 → ℂ)
    (i j : Fin 5) (hij : i ≠ j) (e : Fin 10)
    (hI : (Set.range (fun q : {q : NormalizedSystem ℂ 5 mass | q.InGauge i j} =>
      q.val.fiveBodyFourProduct e)).Infinite) (B : ℝ) :
    ∃ q : NormalizedSystem ℂ 5 mass, q.InGauge i j ∧ B < ‖q.fiveBodyFourProduct e‖ := by
  classical
  by_contra hn
  push Not at hn
  have hf := finite_polynomial_image_of_bounded (PolynomialEncoding.gaugedIdeal mass i j)
    (PolynomialEncoding.fiveBodyFourProductPolynomial e) (by
      refine ⟨B, ?_⟩
      intro x hx
      obtain ⟨he,hg⟩ := (PolynomialEncoding.mem_gauged_zeroLocus_iff mass i j x).mp hx
      let q := PolynomialEncoding.ofCommonZero mass x he
      have hq : q.InGauge i j := ⟨hij,hg⟩
      simpa only [PolynomialEncoding.five_body_four_product_polynomial_eval] using hn q hq)
  apply hI
  apply hf.subset
  rintro _ ⟨q,rfl⟩
  refine ⟨PolynomialEncoding.assignment q.val, ?_, ?_⟩
  · exact (PolynomialEncoding.mem_gauged_zeroLocus_iff mass i j _).mpr
      ⟨PolynomialEncoding.normalized_vanishes q.val,q.property.2⟩
  · simp [PolynomialEncoding.five_body_four_product_polynomial_eval,
      PolynomialEncoding.assignment,PolynomialEncoding.xCoord,PolynomialEncoding.yCoord,
      NormalizedSystem.fiveBodyFourProduct]

theorem NormalizedSystem.four_product_norm_le_source_bound {mass : Fin 5 → ℂ}
    (q : NormalizedSystem ℂ 5 mass) {B : ℝ} (hB : 0 ≤ B)
    (hq : max ‖q.toZW.zSourceVector‖ ‖q.toZW.wSourceVector‖ ≤ B) (e : Fin 10) :
    ‖q.fiveBodyFourProduct e‖ ≤ (4 * B ^ 2) ^ 4 := by
  have hd (k) : ‖fiveBodyDistanceData q.x q.y k‖ ≤ 4 * B ^ 2 :=
    q.squared_distance_norm_le_source_bound hB hq _ _
  have hp : (∏ k : Fin 3, ‖fiveBodyDistanceData q.x q.y (fiveBodyDisjointEdges e k)‖) ≤
      (4 * B ^ 2) ^ 3 := by
    calc
      _ ≤ ∏ _ : Fin 3, 4 * B ^ 2 := Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hd _)
      _ = _ := by simp
  simp only [fiveBodyFourProduct,fiveBodyFourProducts,norm_mul,norm_prod]
  calc
    _ ≤ (4 * B ^ 2) * (4 * B ^ 2) ^ 3 :=
      mul_le_mul (hd e) hp (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) (by positivity)
    _ = _ := by ring

theorem exists_escaping_four_product_sequence_of_infinite_gauged
    (mass : Fin 5 → ℂ) (i j : Fin 5) (hij : i ≠ j)
    (hI : {q : NormalizedSystem ℂ 5 mass | q.InGauge i j}.Infinite) :
    ∃ e : Fin 10, ∃ q : ℕ → NormalizedSystem ℂ 5 mass,
      (∀ t, (q t).InGauge i j) ∧
      Tendsto (fun t => ‖(q t).fiveBodyFourProduct e‖) atTop atTop ∧
      ¬ BddAbove (Set.range
        (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖)) := by
  classical
  obtain ⟨e,he⟩ := exists_infinite_four_product_image_of_infinite_gauged mass i j hI
  choose q hq using fun t : ℕ =>
    exists_large_gauged_four_product_of_infinite_image mass i j hij e he (t : ℝ)
  refine ⟨e,q,fun t => (hq t).1,?_,?_⟩
  · exact tendsto_atTop_mono (fun t => (hq t).2.le) tendsto_natCast_atTop_atTop
  · rintro ⟨B,hB⟩
    obtain ⟨t,ht⟩ := exists_nat_gt ((4 * (max B 0) ^ 2) ^ 4)
    have hbd := (q t).four_product_norm_le_source_bound (le_max_right B 0)
      ((hB (Set.mem_range_self t)).trans (le_max_left B 0)) e
    exact (not_lt_of_ge hbd) (ht.trans (hq t).2)

end
end CentralConfigurations
