import CentralConfigurations.Asymptotics.AlgebraicUnbounded
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite distance data determine finitely many gauged normalized systems

This is the elementary-geometry input used in Section 9.1 to select a
dominant distance polynomial. All pair distances are used here; the stronger
five-of-six observation in Albouy--Kaloshin is not needed for that selection.
The force equations fix translation, while the chosen gauge fixes rotation.
Complex square-root and inverse-distance choices are retained as finite
choices, rather than replaced by a positivity assumption.
-/

namespace CentralConfigurations
noncomputable section
open scoped BigOperators

theorem finite_range_apply {α β γ : Type*} {f : α → β}
    (hf : (Set.range f).Finite) (g : β → γ) : (Set.range (fun a => g (f a))).Finite := by
  simpa only [← Set.range_comp, Function.comp_def] using hf.image g

theorem finite_range_apply_two {α β γ δ : Type*} {f : α → β} {g : α → γ}
    (hf : (Set.range f).Finite) (hg : (Set.range g).Finite) (op : β → γ → δ) :
    (Set.range (fun a => op (f a) (g a))).Finite := by
  apply ((hf.prod hg).image (fun p => op p.1 p.2)).subset
  rintro _ ⟨a, rfl⟩
  exact ⟨(f a, g a), ⟨Set.mem_range_self a, Set.mem_range_self a⟩, rfl⟩

theorem finite_range_functions {α ι β : Type*} [Finite ι] {f : α → ι → β}
    (hf : ∀ i, (Set.range (fun a => f a i)).Finite) : (Set.range f).Finite := by
  apply Set.forall_finite_image_eval_iff.mp
  intro i
  simpa only [← Set.range_comp, Function.comp_def] using hf i

theorem finite_range_of_square {α K : Type*} [CommRing K] [IsDomain K]
    {f : α → K} (hf : (Set.range (fun a => f a ^ 2)).Finite) : (Set.range f).Finite := by
  classical
  have fibers : ∀ c ∈ Set.range (fun a => f a ^ 2), {z : K | z ^ 2 = c}.Finite := by
    rintro c ⟨a, rfl⟩
    apply ((Set.finite_singleton (-f a)).insert (f a)).subset
    intro z hz
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using
      (sq_eq_sq_iff_eq_or_eq_neg.mp hz)
  apply (hf.biUnion fibers).subset
  rintro z ⟨a, rfl⟩
  exact Set.mem_iUnion.mpr ⟨f a ^ 2,
    Set.mem_iUnion.mpr ⟨Set.mem_range_self a, rfl⟩⟩

theorem NormalizedSystem.gauge_x_difference_ne_zero {n : ℕ} {mass : Fin n → ℂ}
    (q : NormalizedSystem ℂ n mass) {i j : Fin n} (hg : q.InGauge i j) :
    q.x i - q.x j ≠ 0 := by
  intro h
  exact q.collision_free hg.1 ⟨sub_eq_zero.mp h, hg.2⟩

theorem NormalizedSystem.gauge_distance_reconstruction {n : ℕ} {mass : Fin n → ℂ}
    (q : NormalizedSystem ℂ n mass) {i j : Fin n} (hg : q.InGauge i j) (a : Fin n) :
    q.x i - q.x a =
      (squaredSeparation q.x q.y i a + squaredSeparation q.x q.y i j -
        squaredSeparation q.x q.y j a) / (2 * (q.x i - q.x j)) := by
  apply (eq_div_iff (mul_ne_zero (by norm_num) (q.gauge_x_difference_ne_zero hg))).mpr
  simp only [squaredSeparation, hg.2]
  ring

theorem finite_gauged_systems_of_finite_distances {n : ℕ} (mass : Fin n → ℂ)
    (i j : Fin n)
    (h : ∀ a b, (Set.range (fun q : {q : NormalizedSystem ℂ n mass | q.InGauge i j} =>
      squaredSeparation q.val.x q.val.y a b)).Finite) :
    {q : NormalizedSystem ℂ n mass | q.InGauge i j}.Finite := by
  classical
  let S := {q : NormalizedSystem ℂ n mass | q.InGauge i j}
  let d : S → Fin n → Fin n → ℂ := fun q a b => squaredSeparation q.val.x q.val.y a b
  let u : S → Fin n → ℂ := fun q a => q.val.x i - q.val.x a
  let v : S → Fin n → ℂ := fun q a => q.val.y i - q.val.y a
  have hd (a b) : (Set.range (fun q : S => d q a b)).Finite := h a b
  have hs : (Set.range (fun q : S => q.val.x i - q.val.x j)).Finite := by
    apply finite_range_of_square
    convert hd i j using 2
    funext q
    dsimp [d]
    simp only [squaredSeparation, q.property.2, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]
  have hu (a) : (Set.range (fun q : S => u q a)).Finite := by
    have hr := finite_range_apply_two
      (finite_range_apply_two (finite_range_apply_two (hd i a) (hd i j) (· + ·))
        (hd j a) (· - ·)) hs (fun x s => x / (2 * s))
    convert hr using 2
    funext q
    exact q.val.gauge_distance_reconstruction q.property a
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

end
end CentralConfigurations
