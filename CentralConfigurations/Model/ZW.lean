import CentralConfigurations.Model.Normalized
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.LinearCombination

/-!
# The branch-free z/w change of coordinates

Chang (2023), Section 2.2, equations (2.2)--(2.3). We keep the inverse-distance
variable delta, so the force terms are delta^3 (z_i-z_j). The metric
equations retain every complex inverse-distance branch.
-/

namespace CentralConfigurations

open scoped BigOperators

/-- Equation (2.3), with force coefficients expressed using delta. -/
structure ZWSystem (K : Type*) [CommRing K] (n : ℕ) (mass : Fin n → K) where
  z : Fin n → K
  w : Fin n → K
  delta : Fin n → Fin n → K
  delta_symm : ∀ i j, delta i j = delta j i
  delta_diagonal : ∀ i, delta i i = 0
  force_z : ∀ i, z i = ∑ j, mass j * delta i j ^ 3 * (z i - z j)
  force_w : ∀ i, w i = ∑ j, mass j * delta i j ^ 3 * (w i - w j)
  distance : ∀ i j, i ≠ j → delta i j ^ 2 * ((z i - z j) * (w i - w j)) = 1

/-- Swapping the two colors preserves the full system. -/
def ZWSystem.swap {K : Type*} [CommRing K] {n : ℕ} {mass : Fin n → K}
    (q : ZWSystem K n mass) : ZWSystem K n mass where
  z := q.w
  w := q.z
  delta := q.delta
  delta_symm := q.delta_symm
  delta_diagonal := q.delta_diagonal
  force_z := q.force_w
  force_w := q.force_z
  distance i j hij := by rw [mul_comm (q.w i - q.w j)]; exact q.distance i j hij

def ZWSystem.zForce {K : Type*} [CommRing K] {n : ℕ} {mass : Fin n → K}
    (q : ZWSystem K n mass) (i j : Fin n) : K :=
  q.delta i j ^ 3 * (q.z i - q.z j)

def ZWSystem.wForce {K : Type*} [CommRing K] {n : ℕ} {mass : Fin n → K}
    (q : ZWSystem K n mass) (i j : Fin n) : K :=
  q.delta i j ^ 3 * (q.w i - q.w j)

/-- A polynomial force/separation identity, with no root choices or cancellation. -/
theorem ZWSystem.wForce_cube_zsep_four {K : Type*} [CommRing K] {n : ℕ}
    {mass : Fin n → K} (q : ZWSystem K n mass) (i j : Fin n) (hij : i ≠ j) :
    q.wForce i j ^ 3 * (q.z i - q.z j) ^ 4 = q.zForce i j := by
  calc
    _ = q.zForce i j *
        (q.delta i j ^ 2 * ((q.z i - q.z j) * (q.w i - q.w j))) ^ 3 := by
      unfold zForce wForce
      ring
    _ = _ := by rw [q.distance i j hij]; ring

theorem ZWSystem.scaled_force_identity {K : Type*} [CommRing K] {n : ℕ}
    {mass : Fin n → K} (q : ZWSystem K n mass) (a : K) (i j : Fin n) (hij : i ≠ j) :
    (a * q.wForce i j) ^ 3 * (a * q.z i - a * q.z j) ^ 4 =
      a ^ 6 * (a * q.zForce i j) := by
  calc
    _ = a ^ 7 * (q.wForce i j ^ 3 * (q.z i - q.z j) ^ 4) := by ring
    _ = _ := by rw [q.wForce_cube_zsep_four i j hij]; ring

theorem zw_separation_identity (a b c d : ℂ) :
    ((a + Complex.I * b) - (c + Complex.I * d)) *
      ((a - Complex.I * b) - (c - Complex.I * d)) =
      (a - c) ^ 2 + (b - d) ^ 2 := by
  calc
    _ = (a - c) ^ 2 - Complex.I ^ 2 * (b - d) ^ 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- The exact complex linear coordinate transformation in Section 2.2. -/
def NormalizedSystem.toZW {n : ℕ} {mass : Fin n → ℂ}
    (q : NormalizedSystem ℂ n mass) : ZWSystem ℂ n mass where
  z i := q.x i + Complex.I * q.y i
  w i := q.x i - Complex.I * q.y i
  delta := q.delta
  delta_symm := q.delta_symm
  delta_diagonal := q.delta_diagonal
  force_z i := by
    calc
      _ = (∑ j, mass j * q.delta i j ^ 3 * (q.x i - q.x j)) +
          Complex.I * (∑ j, mass j * q.delta i j ^ 3 * (q.y i - q.y j)) := by
            rw [← q.force_x i, ← q.force_y i]
      _ = _ := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  force_w i := by
    calc
      _ = (∑ j, mass j * q.delta i j ^ 3 * (q.x i - q.x j)) -
          Complex.I * (∑ j, mass j * q.delta i j ^ 3 * (q.y i - q.y j)) := by
            rw [← q.force_x i, ← q.force_y i]
      _ = _ := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  distance i j hij := by
    rw [zw_separation_identity]
    exact q.distance i j hij

theorem zw_inverse_x (x y : ℂ) :
    ((x + Complex.I * y) + (x - Complex.I * y)) / 2 = x := by ring

theorem zw_inverse_y (x y : ℂ) :
    ((x + Complex.I * y) - (x - Complex.I * y)) / (2 * Complex.I) = y := by
  apply (div_eq_iff (mul_ne_zero (by norm_num) Complex.I_ne_zero)).2
  ring

theorem zw_gauge_iff (xi yi xj yj : ℂ) :
    (xi + Complex.I * yi) - (xj + Complex.I * yj) =
      (xi - Complex.I * yi) - (xj - Complex.I * yj) ↔ yi = yj := by
  constructor
  · intro h
    have hzero : (2 * Complex.I) * (yi - yj) = 0 := by linear_combination h
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left
      (mul_ne_zero (by norm_num) Complex.I_ne_zero))
  · rintro rfl
    ring

theorem inverse_zw_separation (z₁ w₁ z₂ w₂ : ℂ) :
    ((z₁ + w₁) / 2 - (z₂ + w₂) / 2) ^ 2 +
      (Complex.I * (w₁ - z₁) / 2 - Complex.I * (w₂ - z₂) / 2) ^ 2 =
      (z₁ - z₂) * (w₁ - w₂) := by
  calc
    _ = ((z₁ - z₂) + (w₁ - w₂)) ^ 2 / 4 +
        Complex.I ^ 2 * ((w₁ - w₂) - (z₁ - z₂)) ^ 2 / 4 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- The inverse coordinate change also preserves every equation. -/
noncomputable def ZWSystem.toNormalized {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) : NormalizedSystem ℂ n mass where
  x i := (q.z i + q.w i) / 2
  y i := Complex.I * (q.w i - q.z i) / 2
  delta := q.delta
  delta_symm := q.delta_symm
  delta_diagonal := q.delta_diagonal
  force_x i := by
    calc
      _ = ((∑ j, mass j * q.delta i j ^ 3 * (q.z i - q.z j)) +
          (∑ j, mass j * q.delta i j ^ 3 * (q.w i - q.w j))) / 2 := by
            rw [← q.force_z i, ← q.force_w i]
      _ = _ := by
        rw [← Finset.sum_add_distrib]
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring
  force_y i := by
    calc
      _ = Complex.I * ((∑ j, mass j * q.delta i j ^ 3 * (q.w i - q.w j)) -
          (∑ j, mass j * q.delta i j ^ 3 * (q.z i - q.z j))) / 2 := by
            rw [← q.force_z i, ← q.force_w i]
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        simp only [div_eq_mul_inv, Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  distance i j hij := by
    rw [squaredSeparation, inverse_zw_separation]
    exact q.distance i j hij

@[simp] theorem NormalizedSystem.toZW_toNormalized_x {n : ℕ} {mass : Fin n → ℂ}
    (q : NormalizedSystem ℂ n mass) (i : Fin n) : q.toZW.toNormalized.x i = q.x i := by
  exact zw_inverse_x _ _

@[simp] theorem NormalizedSystem.toZW_toNormalized_y {n : ℕ} {mass : Fin n → ℂ}
    (q : NormalizedSystem ℂ n mass) (i : Fin n) : q.toZW.toNormalized.y i = q.y i := by
  change Complex.I * ((q.x i - Complex.I * q.y i) -
    (q.x i + Complex.I * q.y i)) / 2 = q.y i
  calc
    _ = -Complex.I ^ 2 * q.y i := by ring
    _ = _ := by rw [Complex.I_sq]; ring

@[simp] theorem ZWSystem.toNormalized_toZW_z {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i : Fin n) : q.toNormalized.toZW.z i = q.z i := by
  change (q.z i + q.w i) / 2 + Complex.I * (Complex.I * (q.w i - q.z i) / 2) = q.z i
  calc
    _ = (q.z i + q.w i) / 2 + Complex.I ^ 2 * (q.w i - q.z i) / 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

@[simp] theorem ZWSystem.toNormalized_toZW_w {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i : Fin n) : q.toNormalized.toZW.w i = q.w i := by
  change (q.z i + q.w i) / 2 - Complex.I * (Complex.I * (q.w i - q.z i) / 2) = q.w i
  calc
    _ = (q.z i + q.w i) / 2 - Complex.I ^ 2 * (q.w i - q.z i) / 2 := by ring
    _ = _ := by rw [Complex.I_sq]; ring

/-- The reciprocal z/w rescaling used in Section 2.3 preserves the system.
This statement concerns the force and metric equations before fixing a rotational gauge. -/
def ZWSystem.rescale {K : Type*} [Field K] {n : ℕ} {mass : Fin n → K}
    (q : ZWSystem K n mass) (a : K) (ha : a ≠ 0) : ZWSystem K n mass where
  z i := a * q.z i
  w i := a⁻¹ * q.w i
  delta := q.delta
  delta_symm := q.delta_symm
  delta_diagonal := q.delta_diagonal
  force_z i := by
    calc
      _ = a * (∑ j, mass j * q.delta i j ^ 3 * (q.z i - q.z j)) := by rw [← q.force_z i]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  force_w i := by
    calc
      _ = a⁻¹ * (∑ j, mass j * q.delta i j ^ 3 * (q.w i - q.w j)) := by rw [← q.force_w i]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
  distance i j hij := by
    calc
      _ = (a * a⁻¹) * (q.delta i j ^ 2 * ((q.z i - q.z j) * (q.w i - q.w j))) := by ring
      _ = _ := by rw [mul_inv_cancel₀ ha, one_mul, q.distance i j hij]

theorem ZWSystem.z_separation_ne_zero {K : Type*} [CommRing K] [Nontrivial K]
    {n : ℕ} {mass : Fin n → K} (q : ZWSystem K n mass)
    {i j : Fin n} (hij : i ≠ j) : q.z i - q.z j ≠ 0 := by
  intro h
  have hd := q.distance i j hij
  simp [h] at hd

theorem ZWSystem.w_separation_ne_zero {K : Type*} [CommRing K] [Nontrivial K]
    {n : ℕ} {mass : Fin n → K} (q : ZWSystem K n mass)
    {i j : Fin n} (hij : i ≠ j) : q.w i - q.w j ≠ 0 := by
  intro h
  have hd := q.distance i j hij
  simp [h] at hd

end CentralConfigurations
