import CentralConfigurations.Asymptotics.FourProductDominance

/-! Finite inverse-distance and complex square-root choices on any gauged subset.
The finite-recovery argument applies to subsets, including a fixed potential level. -/
namespace CentralConfigurations
noncomputable section
open scoped BigOperators

theorem finite_gauged_subset_of_finite_distances {n : ℕ} (mass : Fin n → ℂ)
    (i j : Fin n) (A : Set (NormalizedSystem ℂ n mass))
    (hA : ∀ q ∈ A, q.InGauge i j)
    (h : ∀ a b, (Set.range (fun q : A =>
      squaredSeparation q.val.x q.val.y a b)).Finite) : A.Finite := by
  classical
  let S := A
  let d : S → Fin n → Fin n → ℂ := fun q a b => squaredSeparation q.val.x q.val.y a b
  let u : S → Fin n → ℂ := fun q a => q.val.x i - q.val.x a
  let v : S → Fin n → ℂ := fun q a => q.val.y i - q.val.y a
  have hd (a b) : (Set.range (fun q : S => d q a b)).Finite := h a b
  have hs : (Set.range (fun q : S => q.val.x i - q.val.x j)).Finite := by
    apply finite_range_of_square
    convert hd i j using 2
    funext q
    dsimp [d]
    simp only [squaredSeparation, (hA q.val q.property).2, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]
  have hu (a) : (Set.range (fun q : S => u q a)).Finite := by
    have hr := finite_range_apply_two
      (finite_range_apply_two (finite_range_apply_two (hd i a) (hd i j) (· + ·))
        (hd j a) (· - ·)) hs (fun x s => x / (2 * s))
    convert hr using 2
    funext q
    exact q.val.gauge_distance_reconstruction (hA q.val q.property) a
  have hv (a) : (Set.range (fun q : S => v q a)).Finite := by
    apply finite_range_of_square
    have hr := finite_range_apply_two (hd i a) (hu a) (fun d u => d - u ^ 2)
    convert hr using 2
    funext q
    dsimp [u, v, d, squaredSeparation]
    ring
  have hdelta (a b) : (Set.range (fun q : S => q.val.delta a b)).Finite := by
    by_cases hab : a = b
    · subst b
      have he : (fun q : S => q.val.delta a a) = fun _ => (0 : ℂ) := by
        funext q
        exact q.val.delta_diagonal a
      rw [he]
      exact Set.finite_range_const
    · apply finite_range_of_square
      have hr := finite_range_apply (hd a b) (fun z => z⁻¹)
      convert hr using 2
      funext q
      apply (mul_right_cancel₀ (q.val.separation_ne_zero hab))
      rw [inv_mul_cancel₀ (q.val.separation_ne_zero hab)]
      exact q.val.distance a b hab
  have hx (a) : (Set.range (fun q : S => q.val.x a)).Finite := by
    have ht (b) := finite_range_apply_two (hdelta a b)
      (finite_range_apply_two (hu b) (hu a) (· - ·))
      (fun delta diff => mass b * delta ^ 3 * diff)
    have hr := finite_range_apply (finite_range_functions ht) (fun f => ∑ b, f b)
    convert hr using 2
    funext q
    rw [q.val.force_x a]
    apply Finset.sum_congr rfl
    intro b _
    dsimp [u]
    ring
  have hy (a) : (Set.range (fun q : S => q.val.y a)).Finite := by
    have ht (b) := finite_range_apply_two (hdelta a b)
      (finite_range_apply_two (hv b) (hv a) (· - ·))
      (fun delta diff => mass b * delta ^ 3 * diff)
    have hr := finite_range_apply (finite_range_functions ht) (fun f => ∑ b, f b)
    convert hr using 2
    funext q
    rw [q.val.force_y a]
    apply Finset.sum_congr rfl
    intro b _
    dsimp [v]
    ring
  have ha : (Set.range (fun q : S => PolynomialEncoding.assignment q.val)).Finite := by
    apply finite_range_functions
    rintro (a | (a | ⟨a, b⟩))
    · exact hx a
    · exact hy a
    · exact hdelta a b
  have hi : Function.Injective (fun q : S => PolynomialEncoding.assignment q.val) := by
    intro q r hqr
    apply Subtype.ext
    apply (PolynomialEncoding.commonZeroEquiv mass).injective
    exact Subtype.ext hqr
  haveI : Finite S := (Set.finite_range_iff hi).mp ha
  exact Set.toFinite _


theorem finite_gauged_five_body_subset_of_finite_four_products (mass : Fin 5 → ℂ)
    (i j : Fin 5) (A : Set (NormalizedSystem ℂ 5 mass))
    (hA : ∀ q ∈ A, q.InGauge i j)
    (h : ∀ e, (Set.range (fun q : A => q.val.fiveBodyFourProduct e)).Finite) : A.Finite := by
  have hd := finite_distance_images_of_finite_four_product_images
    (fun q : A => fiveBodyDistanceData q.val.x q.val.y)
    (fun q e => q.val.separation_ne_zero (five_body_edge_distinct e)) h
  apply finite_gauged_subset_of_finite_distances mass i j A hA
  intro a b
  by_cases hab : a = b
  · subst b
    simpa only [squaredSeparation, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero] using
      (Set.finite_range_const : (Set.range (fun _ : A => (0 : ℂ))).Finite)
  · obtain ⟨e, he⟩ := five_body_distance_data_coverage a b hab
    simpa only [he] using hd e

end
end CentralConfigurations
