import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Tactic.Ring

/-!
# Polynomial normalized central configurations

Equation (2.2) of Chang (2023). Differences in the force equation use
q_k - q_l. The omitted diagonal term is zero, so finite sums can include it.
The inverse-distance entries are stored symmetrically with diagonal fixed to
zero, so the representation introduces no extra free coordinates. Positivity
and the real physical interpretation are separate.
-/

namespace CentralConfigurations

open scoped BigOperators

/-- The squared separation polynomial, over either real or complex coordinates. -/
def squaredSeparation {K : Type*} [CommRing K] {n : ℕ}
    (x y : Fin n → K) (i j : Fin n) : K :=
  (x i - x j) ^ 2 + (y i - y j) ^ 2

/-- The polynomial equations before imposing a rotational gauge. -/
structure NormalizedSystem (K : Type*) [CommRing K] (n : ℕ) (mass : Fin n → K) where
  x : Fin n → K
  y : Fin n → K
  delta : Fin n → Fin n → K
  delta_symm : ∀ i j, delta i j = delta j i
  delta_diagonal : ∀ i, delta i i = 0
  force_x : ∀ i, x i = ∑ j, mass j * delta i j ^ 3 * (x i - x j)
  force_y : ∀ i, y i = ∑ j, mass j * delta i j ^ 3 * (y i - y j)
  distance : ∀ i j, i ≠ j →
    delta i j ^ 2 * squaredSeparation x y i j = 1

/-- Canonical zero-diagonal extension does not restrict the original off-diagonal
equations: their diagonal force terms already vanish. -/
def NormalizedSystem.ofOffDiagonal {K : Type*} [CommRing K] {n : ℕ}
    (mass x y : Fin n → K) (d : Fin n → Fin n → K)
    (hs : ∀ i j, d i j = d j i)
    (hx : ∀ i, x i = ∑ j, mass j * d i j ^ 3 * (x i - x j))
    (hy : ∀ i, y i = ∑ j, mass j * d i j ^ 3 * (y i - y j))
    (hd : ∀ i j, i ≠ j → d i j ^ 2 * squaredSeparation x y i j = 1) :
    NormalizedSystem K n mass where
  x := x
  y := y
  delta i j := if i = j then 0 else d i j
  delta_symm i j := by
    by_cases hij : i = j
    · subst j
      rfl
    · simp [hij, Ne.symm hij, hs i j]
  delta_diagonal i := by simp
  force_x i := by
    calc
      x i = ∑ j, mass j * d i j ^ 3 * (x i - x j) := hx i
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j <;> simp [hij]
  force_y i := by
    calc
      y i = ∑ j, mass j * d i j ^ 3 * (y i - y j) := hy i
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j <;> simp [hij]
  distance i j hij := by simpa [hij] using hd i j hij

/-- A chosen pair fixes the rotational gauge in (2.2). -/
def NormalizedSystem.InGauge {K : Type*} [CommRing K] {n : ℕ}
    {mass : Fin n → K} (q : NormalizedSystem K n mass) (i j : Fin n) : Prop :=
  i ≠ j ∧ q.y i = q.y j

theorem NormalizedSystem.delta_ne_zero {K : Type*} [CommRing K] [Nontrivial K]
    {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass)
    {i j : Fin n} (hij : i ≠ j) : q.delta i j ≠ 0 := by
  intro h
  have hd := q.distance i j hij
  simp [h] at hd

theorem NormalizedSystem.separation_ne_zero {K : Type*} [CommRing K] [Nontrivial K]
    {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass)
    {i j : Fin n} (hij : i ≠ j) : squaredSeparation q.x q.y i j ≠ 0 := by
  intro h
  have hd := q.distance i j hij
  simp [h] at hd

theorem NormalizedSystem.collision_free {K : Type*} [CommRing K] [Nontrivial K]
    {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass)
    {i j : Fin n} (hij : i ≠ j) : ¬ (q.x i = q.x j ∧ q.y i = q.y j) := by
  rintro ⟨hx, hy⟩
  apply q.separation_ne_zero hij
  simp [squaredSeparation, hx, hy]

/-- Pair forces cancel in the mass-weighted sum. -/
theorem weighted_force_sum_zero {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    {n : ℕ} (mass pos : Fin n → K) (delta : Fin n → Fin n → K)
    (hs : ∀ i j, delta i j = delta j i) :
    ∑ i, mass i * (∑ j, mass j * delta i j ^ 3 * (pos i - pos j)) = 0 := by
  simp only [Finset.mul_sum]
  apply CharZero.eq_neg_self_iff.mp
  rw [← Finset.sum_neg_distrib]
  calc
    (∑ i, ∑ j, mass i * (mass j * delta i j ^ 3 * (pos i - pos j))) =
        ∑ j, ∑ i, mass i * (mass j * delta i j ^ 3 * (pos i - pos j)) :=
      Finset.sum_comm
    _ = ∑ j, -(∑ i, mass j * (mass i * delta j i ^ 3 * (pos j - pos i))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hs i j]
      ring

theorem NormalizedSystem.mass_center_x {K : Type*} [CommRing K] [IsDomain K]
    [CharZero K] {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass) :
    ∑ i, mass i * q.x i = 0 := by
  calc
    _ = ∑ i, mass i * (∑ j, mass j * q.delta i j ^ 3 * (q.x i - q.x j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← q.force_x i]
    _ = 0 := weighted_force_sum_zero mass q.x q.delta q.delta_symm

theorem NormalizedSystem.mass_center_y {K : Type*} [CommRing K] [IsDomain K]
    [CharZero K] {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass) :
    ∑ i, mass i * q.y i = 0 := by
  calc
    _ = ∑ i, mass i * (∑ j, mass j * q.delta i j ^ 3 * (q.y i - q.y j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← q.force_y i]
    _ = 0 := weighted_force_sum_zero mass q.y q.delta q.delta_symm

end CentralConfigurations
