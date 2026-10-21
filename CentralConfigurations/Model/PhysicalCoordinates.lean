import CentralConfigurations.Model.PhysicalNormalization
import Mathlib.Analysis.Complex.Norm

/-!
# Newtonian coordinates and the positive polynomial branch

The input uses the actual positive Euclidean distance sqrt(dx² + dy²).
Translations, positive scaling, and rotations produce a gauged normalized
system. Inverse-distance variables are constructed, not supplied independently.
-/

namespace CentralConfigurations

open scoped BigOperators

noncomputable def physicalInverseDistance {n : ℕ} (x y : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (Real.sqrt (squaredSeparation x y i j))⁻¹

theorem physicalInverseDistance_eq_inv_norm {n : ℕ} (x y : Fin n → ℝ) (i j : Fin n) :
    physicalInverseDistance x y i j =
      ‖(⟨x i, y i⟩ : ℂ) - (⟨x j, y j⟩ : ℂ)‖⁻¹ := by
  simp only [physicalInverseDistance, Complex.norm_def, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, squaredSeparation, pow_two]

theorem squaredSeparation_sub_const {K : Type*} [CommRing K] {n : ℕ}
    (x y : Fin n → K) (cx cy : K) (i j : Fin n) :
    squaredSeparation (fun k => x k - cx) (fun k => y k - cy) i j =
      squaredSeparation x y i j := by
  unfold squaredSeparation
  ring

/-- The unnormalized real force equations, allowing an arbitrary origin.
The equations below will force the given center to be the mass center. -/
structure PhysicalCentralConfiguration (n : ℕ) (mass : Fin n → ℝ) where
  x : Fin n → ℝ
  y : Fin n → ℝ
  centerX : ℝ
  centerY : ℝ
  multiplier : ℝ
  separated : ∀ i j, i ≠ j → 0 < squaredSeparation x y i j
  force_x : ∀ i, multiplier * (x i - centerX) =
    ∑ j, mass j * physicalInverseDistance x y i j ^ 3 * (x i - x j)
  force_y : ∀ i, multiplier * (y i - centerY) =
    ∑ j, mass j * physicalInverseDistance x y i j ^ 3 * (y i - y j)

namespace PhysicalCentralConfiguration

variable {n : ℕ} {mass : Fin n → ℝ} (q : PhysicalCentralConfiguration n mass)

noncomputable def toCentered : RealCentralSystem n mass where
  x i := q.x i - q.centerX
  y i := q.y i - q.centerY
  delta := physicalInverseDistance q.x q.y
  multiplier := q.multiplier
  delta_symm i j := by
    unfold physicalInverseDistance
    congr 2
    unfold squaredSeparation
    ring
  delta_diagonal i := by simp [physicalInverseDistance, squaredSeparation]
  delta_pos i j hij := inv_pos.mpr (Real.sqrt_pos.mpr (q.separated i j hij))
  force_x i := by
    rw [q.force_x i]
    apply Finset.sum_congr rfl
    intro j _
    ring
  force_y i := by
    rw [q.force_y i]
    apply Finset.sum_congr rfl
    intro j _
    ring
  distance i j hij := by
    rw [squaredSeparation_sub_const]
    unfold physicalInverseDistance
    rw [inv_pow, Real.sq_sqrt (le_of_lt (q.separated i j hij))]
    exact inv_mul_cancel₀ (ne_of_gt (q.separated i j hij))

theorem multiplier_pos (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j) :
    0 < q.multiplier := q.toCentered.multiplier_pos hm i j hij

theorem centerX_is_mass_center (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j) :
    ∑ k, mass k * (q.x k - q.centerX) = 0 := by
  have hf : q.multiplier * (∑ k, mass k * (q.x k - q.centerX)) = 0 := by
    calc
      _ = ∑ k, mass k * (q.multiplier * (q.x k - q.centerX)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ k, mass k * (∑ l, mass l * q.toCentered.delta k l ^ 3 * (q.x k - q.x l)) := by
        simp_rw [q.force_x]
        rfl
      _ = 0 := weighted_force_sum_zero mass q.x _ q.toCentered.delta_symm
  exact (mul_eq_zero.mp hf).resolve_left (ne_of_gt (q.multiplier_pos hm i j hij))

theorem centerY_is_mass_center (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j) :
    ∑ k, mass k * (q.y k - q.centerY) = 0 := by
  have hf : q.multiplier * (∑ k, mass k * (q.y k - q.centerY)) = 0 := by
    calc
      _ = ∑ k, mass k * (q.multiplier * (q.y k - q.centerY)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ k, mass k * (∑ l, mass l * q.toCentered.delta k l ^ 3 * (q.y k - q.y l)) := by
        simp_rw [q.force_y]
        rfl
      _ = 0 := weighted_force_sum_zero mass q.y _ q.toCentered.delta_symm
  exact (mul_eq_zero.mp hf).resolve_left (ne_of_gt (q.multiplier_pos hm i j hij))

theorem exists_gauged_normalization (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ (s a b : ℝ) (p : NormalizedSystem ℝ n mass),
      0 < s ∧ s ^ 3 = q.multiplier ∧ a ^ 2 + b ^ 2 = 1 ∧
      p.InGauge i j ∧ 0 < p.x i - p.x j ∧
      (∀ k, p.x k = s * (a * (q.x k - q.centerX) + b * (q.y k - q.centerY))) ∧
      (∀ k, p.y k = s * (-b * (q.x k - q.centerX) + a * (q.y k - q.centerY))) ∧
      (∀ k l, p.delta k l = physicalInverseDistance q.x q.y k l / s) ∧
      (∀ k l, k ≠ l → 0 < p.delta k l) :=
  q.toCentered.exists_gauged_normalization hm i j hij

end PhysicalCentralConfiguration
end CentralConfigurations
