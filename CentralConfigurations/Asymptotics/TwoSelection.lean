import CentralConfigurations.Asymptotics.AlgebraicUnbounded
import CentralConfigurations.Asymptotics.Unbounded

/-!
# Two polynomial selections on one affine algebraic set

A finite family of polynomial units determines finite fibers. A local
subsequence theorem sends every pole of a family member to zero for a fixed
positive product of members. The first selection proves that this product
has infinite image; the second selects its pole and derives a contradiction.
No irreducible component, smooth point, or curve extraction is used.
-/

namespace CentralConfigurations
noncomputable section
open scoped BigOperators Topology
open Filter

theorem exists_polynomial_pole_sequence {σ : Type*} [Finite σ]
    (I : Ideal (MvPolynomial σ ℂ)) (p : MvPolynomial σ ℂ)
    (hI : ((fun x => MvPolynomial.aeval x p) '' MvPolynomial.zeroLocus ℂ I).Infinite) :
    ∃ x : ℕ → σ → ℂ, (∀ t, x t ∈ MvPolynomial.zeroLocus ℂ I) ∧
      Tendsto (fun t => ‖MvPolynomial.aeval (x t) p‖) atTop atTop := by
  classical
  have hlarge (B : ℝ) : ∃ x ∈ MvPolynomial.zeroLocus ℂ I,
      B < ‖MvPolynomial.aeval x p‖ := by
    by_contra hn
    push Not at hn
    exact hI (finite_polynomial_image_of_bounded I p ⟨B, hn⟩)
  choose x hx using fun t : ℕ => hlarge (t : ℝ)
  exact ⟨x, fun t => (hx t).1,
    tendsto_atTop_mono (fun t => (hx t).2.le) tendsto_natCast_atTop_atTop⟩

theorem exists_positive_product_factor_pole_subsequence {ι : Type*}
    (R : Finset ι) (f : ℕ → ι → ℂ)
    (hP : Tendsto (fun t => ‖∏ e ∈ R, f t e‖) atTop atTop) :
    ∃ e ∈ R, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun t => ‖f (φ t) e‖) atTop atTop := by
  classical
  have hn : ¬ ∀ e ∈ R, BddAbove (Set.range (fun t => ‖f t e‖)) := by
    intro h
    have hb : ∀ e, ∃ B : ℝ, ∀ t, e ∈ R → ‖f t e‖ ≤ B := by
      intro e
      by_cases he : e ∈ R
      · obtain ⟨B, hB⟩ := h e he
        exact ⟨B, fun t _ => hB (Set.mem_range_self t)⟩
      · exact ⟨0, fun _ hm => (he hm).elim⟩
    choose B hB using hb
    have hbound (t : ℕ) : ‖∏ e ∈ R, f t e‖ ≤ ∏ e ∈ R, max (B e) 0 := by
      rw [norm_prod]
      apply Finset.prod_le_prod (fun _ _ => norm_nonneg _)
      intro e he
      exact (hB e t he).trans (le_max_left _ _)
    obtain ⟨t, ht⟩ := (hP.eventually (eventually_gt_atTop (∏ e ∈ R, max (B e) 0))).exists
    exact not_lt_of_ge (hbound t) ht
  push Not at hn
  obtain ⟨e, he, hne⟩ := hn
  obtain ⟨φ, hφ, hpole⟩ := unbounded_real_subsequence (fun t => ‖f t e‖) hne
  exact ⟨e, he, φ, hφ, hpole⟩

theorem finite_affine_set_of_two_selections {σ ι : Type*} [Finite σ] [Finite ι]
    (I : Ideal (MvPolynomial σ ℂ)) (f : ι → MvPolynomial σ ℂ) (R : Finset ι)
    (hdet : (∀ e, ((fun x => MvPolynomial.aeval x (f e)) ''
      MvPolynomial.zeroLocus ℂ I).Finite) → (MvPolynomial.zeroLocus ℂ I).Finite)
    (hunit : ∀ x ∈ MvPolynomial.zeroLocus ℂ I, ∀ e ∈ R,
      MvPolynomial.aeval x (f e) ≠ 0)
    (hdecay : ∀ (x : ℕ → σ → ℂ), (∀ t, x t ∈ MvPolynomial.zeroLocus ℂ I) →
      ∀ e, Tendsto (fun t => ‖MvPolynomial.aeval (x t) (f e)‖) atTop atTop →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun t => MvPolynomial.aeval (x (φ t)) (∏ k ∈ R, f k)) atTop (𝓝 0)) :
    (MvPolynomial.zeroLocus ℂ I).Finite := by
  classical
  by_contra hInfinite
  have hobs : ∃ e, ((fun x => MvPolynomial.aeval x (f e)) ''
      MvPolynomial.zeroLocus ℂ I).Infinite := by
    by_contra hn
    push Not at hn
    exact hInfinite (hdet hn)
  obtain ⟨e, he⟩ := hobs
  obtain ⟨x, hx, hpole⟩ := exists_polynomial_pole_sequence I (f e) he
  obtain ⟨φ, hφ, hzero⟩ := hdecay x hx e hpole
  let P := ∏ k ∈ R, f k
  have hPInfinite : ((fun a => MvPolynomial.aeval a P) ''
      MvPolynomial.zeroLocus ℂ I).Infinite := by
    intro hfinite
    have hmem : (0 : ℂ) ∈ ((fun a => MvPolynomial.aeval a P) ''
        MvPolynomial.zeroLocus ℂ I) :=
      hfinite.isClosed.mem_of_tendsto hzero
        (Eventually.of_forall (fun t => ⟨x (φ t), hx (φ t), rfl⟩))
    obtain ⟨a, ha, hPa⟩ := hmem
    have hnonzero : MvPolynomial.aeval a P ≠ 0 := by
      simp only [P, map_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun k hk => hunit a ha k hk)
    exact hnonzero hPa
  obtain ⟨y, hy, hPpole⟩ := exists_polynomial_pole_sequence I P hPInfinite
  have hp : Tendsto (fun t => ‖∏ k ∈ R, MvPolynomial.aeval (y t) (f k)‖)
      atTop atTop := by simpa only [P, map_prod] using hPpole
  obtain ⟨k, _, ψ, hψ, hkPole⟩ :=
    exists_positive_product_factor_pole_subsequence R
      (fun t k => MvPolynomial.aeval (y t) (f k)) hp
  obtain ⟨χ, hχ, hPzero⟩ := hdecay (fun t => y (ψ t)) (fun t => hy (ψ t)) k hkPole
  have hnormzero : Tendsto (fun t => ‖MvPolynomial.aeval (y (ψ (χ t))) P‖)
      atTop (𝓝 0) := by
    simpa only [norm_zero] using hPzero.norm
  have hnormpole : Tendsto (fun t => ‖MvPolynomial.aeval (y (ψ (χ t))) P‖)
      atTop atTop := hPpole.comp (hψ.comp hχ).tendsto_atTop
  exact not_tendsto_atTop_of_tendsto_nhds hnormzero hnormpole

end
end CentralConfigurations
