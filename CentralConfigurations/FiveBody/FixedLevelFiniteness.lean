import CentralConfigurations.Model.FixedPotentialLevel
import CentralConfigurations.Model.FiniteGaugeSubset
import CentralConfigurations.Asymptotics.TwoSelection

/-!
# Curve-free finite fixed-level fibers

The analytic boundary is the subsequence decay statement for a selected
escaping original four-product, on the exact same potential level. It does
not assert decay for every unbounded source sequence.
-/

namespace CentralConfigurations
noncomputable section
open scoped BigOperators Topology
open Filter

def NormalizedSystem.fiveBodySelectedProduct {mass : Fin 5 → ℂ}
    (q : NormalizedSystem ℂ 5 mass) (R : Finset (Fin 10)) : ℂ :=
  ∏ e ∈ R, q.fiveBodyFourProduct e

theorem NormalizedSystem.fiveBodySelectedProduct_ne_zero {mass : Fin 5 → ℂ}
    (q : NormalizedSystem ℂ 5 mass) (R : Finset (Fin 10)) :
    q.fiveBodySelectedProduct R ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun e _ => q.five_body_four_product_ne_zero e)

theorem assignment_injective {n : ℕ} (mass : Fin n → ℂ) :
    Function.Injective (PolynomialEncoding.assignment (mass := mass)) := by
  intro q r hqr
  apply (PolynomialEncoding.commonZeroEquiv mass).injective
  exact Subtype.ext hqr

theorem finite_fixedPotential_zeroLocus_of_finite_four_product_images
    (mass : Fin 5 → ℂ) (i j : Fin 5) (hij : i ≠ j) (c : ℂ)
    (h : ∀ e, ((fun x => MvPolynomial.aeval x
      (PolynomialEncoding.fiveBodyFourProductPolynomial e)) ''
      MvPolynomial.zeroLocus ℂ (PolynomialEncoding.fixedPotentialIdeal mass i j c)).Finite) :
    (MvPolynomial.zeroLocus ℂ (PolynomialEncoding.fixedPotentialIdeal mass i j c)).Finite := by
  have hr : ∀ e, (Set.range (fun q : fixedPotentialGauge mass i j c =>
      q.val.fiveBodyFourProduct e)).Finite := by
    intro e
    apply (h e).subset
    rintro _ ⟨q, rfl⟩
    refine ⟨PolynomialEncoding.assignment q.val,
      fixedPotential_assignment_mem q.val q.property, ?_⟩
    simp [PolynomialEncoding.five_body_four_product_polynomial_eval,
      PolynomialEncoding.assignment, PolynomialEncoding.xCoord, PolynomialEncoding.yCoord,
      NormalizedSystem.fiveBodyFourProduct]
  have hf := finite_gauged_five_body_subset_of_finite_four_products mass i j
    (fixedPotentialGauge mass i j c) (fun _ hq => hq.1) hr
  apply (hf.image PolynomialEncoding.assignment).subset
  intro a ha
  obtain ⟨q, hq, hqa⟩ := fixedPotential_ofCommonZero_mem mass i j hij c a ha
  exact ⟨q, hq, hqa⟩

/-- Precise local analytic interface: a pole of one original AK four-product
has a subsequence on which the complete fixed positive product decays.
Diagram classification, exclusions, and D5 decay must prove this premise.
The selected original factor at the second end may differ from the first. -/
def FixedLevelFourProductDecay (mass : Fin 5 → ℂ) (i j : Fin 5) (c : ℂ)
    (R : Finset (Fin 10)) : Prop :=
  ∀ q : ℕ → NormalizedSystem ℂ 5 mass,
    (∀ t, q t ∈ fixedPotentialGauge mass i j c) →
    ∀ e, Tendsto (fun t => ‖(q t).fiveBodyFourProduct e‖) atTop atTop →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun t => (q (φ t)).fiveBodySelectedProduct R) atTop (𝓝 0)

theorem finite_fixedPotentialGauge_of_four_product_decay (mass : Fin 5 → ℂ)
    (i j : Fin 5) (hij : i ≠ j) (c : ℂ) (R : Finset (Fin 10))
    (hdecay : FixedLevelFourProductDecay mass i j c R) :
    (fixedPotentialGauge mass i j c).Finite := by
  classical
  have hf : (MvPolynomial.zeroLocus ℂ
      (PolynomialEncoding.fixedPotentialIdeal mass i j c)).Finite := by
    apply finite_affine_set_of_two_selections
      (PolynomialEncoding.fixedPotentialIdeal mass i j c)
      PolynomialEncoding.fiveBodyFourProductPolynomial R
    · exact finite_fixedPotential_zeroLocus_of_finite_four_product_images mass i j hij c
    · intro a ha e _
      obtain ⟨q, _, hqa⟩ := fixedPotential_ofCommonZero_mem mass i j hij c a ha
      rw [← hqa]
      simpa [PolynomialEncoding.five_body_four_product_polynomial_eval,
        PolynomialEncoding.assignment, PolynomialEncoding.xCoord, PolynomialEncoding.yCoord,
        NormalizedSystem.fiveBodyFourProduct] using
        q.five_body_four_product_ne_zero e
    · intro x hx e hpole
      choose q hq using fun t => fixedPotential_ofCommonZero_mem mass i j hij c (x t) (hx t)
      have heval (t : ℕ) (k : Fin 10) : MvPolynomial.aeval (x t)
          (PolynomialEncoding.fiveBodyFourProductPolynomial k) =
          (q t).fiveBodyFourProduct k := by
        rw [← (hq t).2]
        simp [PolynomialEncoding.five_body_four_product_polynomial_eval,
          PolynomialEncoding.assignment, PolynomialEncoding.xCoord, PolynomialEncoding.yCoord,
          NormalizedSystem.fiveBodyFourProduct]
      obtain ⟨φ, hφ, hzero⟩ := hdecay q (fun t => (hq t).1) e (by
        simpa only [heval] using hpole)
      refine ⟨φ, hφ, ?_⟩
      simpa only [map_prod, heval, NormalizedSystem.fiveBodySelectedProduct] using hzero
  apply (Set.finite_image_iff (assignment_injective mass).injOn).mp
  exact hf.subset (by
    rintro a ⟨q, hq, rfl⟩
    exact fixedPotential_assignment_mem q hq)

/-- Finitely many potential values reduce any invariant-selected physical
part of the gauge to finitely many level fibers. -/
theorem finite_gauge_on_selected_potential_values {n : ℕ} (mass : Fin n → ℂ)
    (i j : Fin n) (C : Set ℂ)
    (hlevel : ∀ c ∈ C, (fixedPotentialGauge mass i j c).Finite) :
    {q : NormalizedSystem ℂ n mass | q.InGauge i j ∧ q.unorderedPotential ∈ C}.Finite := by
  let V := Set.range (fun q : NormalizedSystem ℂ n mass => q.unorderedPotential)
  have hV : V.Finite := NormalizedSystem.finite_potential_values mass
  have hf : (⋃ c ∈ V ∩ C, fixedPotentialGauge mass i j c).Finite :=
    (hV.inter_of_left C).biUnion (fun c hc => hlevel c hc.2)
  apply hf.subset
  intro q hq
  exact Set.mem_iUnion.mpr ⟨q.unorderedPotential,
    Set.mem_iUnion.mpr ⟨⟨Set.mem_range_self q, hq.2⟩, hq.1, rfl⟩⟩

end
end CentralConfigurations
