import CentralConfigurations.Model.Virial
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp

/-!
# The differential identity behind Chang's Lemma 2.2

For a solution over a characteristic-zero field extension, every derivation
annihilating the masses also annihilates the potential. Differentiating the
distance equations and symmetrizing the force equations gives d(2U + I) = 0.
Together with U = I, this yields dU = 0. PotentialFiniteness.lean applies
this stationarity identity at generic points to prove finite potential values.
-/

namespace CentralConfigurations

open scoped BigOperators

theorem coordinate_variation {K : Type*} [CommRing K] {n : ℕ}
    (mass pos vel : Fin n → K) (delta : Fin n → Fin n → K)
    (hs : ∀ i j, delta i j = delta j i) :
    (∑ i, ∑ j, mass i * mass j * delta i j ^ 3 * (pos i - pos j) * (vel i - vel j)) =
      2 * (∑ i, mass i * vel i *
        (∑ j, mass j * delta i j ^ 3 * (pos i - pos j))) := by
  calc
    _ = ∑ i, ∑ j,
        (mass i * vel i * (mass j * delta i j ^ 3 * (pos i - pos j)) +
         mass j * vel j * (mass i * delta j i ^ 3 * (pos j - pos i))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hs j i]
      ring
    _ = 2 * (∑ i, ∑ j,
        mass i * vel i * (mass j * delta i j ^ 3 * (pos i - pos j))) :=
      double_sum_symmetrize _
    _ = _ := by simp only [Finset.mul_sum]

namespace NormalizedSystem

variable {R K : Type*} [CommRing R] [Field K] [CharZero K] [Algebra R K]
variable {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass)
variable (D : Derivation R K K)

theorem derivation_delta (i j : Fin n) :
    D (q.delta i j) = -q.delta i j ^ 3 *
      ((q.x i - q.x j) * (D (q.x i) - D (q.x j)) +
       (q.y i - q.y j) * (D (q.y i) - D (q.y j))) := by
  by_cases hij : i = j
  · subst j
    simp [q.delta_diagonal]
  have hd := q.distance i j hij
  have hD := congrArg D hd
  simp only [Derivation.leibniz, Derivation.leibniz_pow, map_add, map_sub,
    Derivation.map_one_eq_zero, smul_eq_mul, Nat.reduceSub, pow_one,
    nsmul_eq_mul, Nat.cast_ofNat, squaredSeparation] at hD
  dsimp [squaredSeparation] at hd
  have he : (2 : K) * (D (q.delta i j) + q.delta i j ^ 3 *
      ((q.x i - q.x j) * (D (q.x i) - D (q.x j)) +
       (q.y i - q.y j) * (D (q.y i) - D (q.y j)))) = 0 := by
    linear_combination q.delta i j * hD - 2 * D (q.delta i j) * hd
  have hz := (mul_eq_zero.mp he).resolve_left (by norm_num : (2 : K) ≠ 0)
  linear_combination hz

omit [CharZero K] in
theorem derivation_inertia (hm : ∀ i, D (mass i) = 0) :
    D q.inertia = 2 * ∑ i,
      (mass i * q.x i * D (q.x i) + mass i * q.y i * D (q.y i)) := by
  unfold inertia
  simp only [map_sum, Derivation.leibniz, Derivation.leibniz_pow, map_add, hm,
    smul_eq_mul, mul_zero, add_zero, Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem derivation_doubledPotential (hm : ∀ i, D (mass i) = 0) :
    D q.doubledPotential = -D q.inertia := by
  have hpair (i j : Fin n) :
      D (if i = j then 0 else mass i * mass j * q.delta i j) =
        -(mass i * mass j * q.delta i j ^ 3 * (q.x i - q.x j) *
            (D (q.x i) - D (q.x j)) +
          mass i * mass j * q.delta i j ^ 3 * (q.y i - q.y j) *
            (D (q.y i) - D (q.y j))) := by
    by_cases hij : i = j
    · subst j
      simp
    · simp only [if_neg hij, Derivation.leibniz, hm, smul_eq_mul, mul_zero,
        add_zero, q.derivation_delta D i j]
      ring
  calc
    _ = -(∑ i, ∑ j,
        mass i * mass j * q.delta i j ^ 3 * (q.x i - q.x j) *
          (D (q.x i) - D (q.x j))) -
        (∑ i, ∑ j,
        mass i * mass j * q.delta i j ^ 3 * (q.y i - q.y j) *
          (D (q.y i) - D (q.y j))) := by
      simp only [doubledPotential, map_sum, hpair, Finset.sum_neg_distrib,
        Finset.sum_add_distrib]
      ring
    _ = -(2 * (∑ i, mass i * D (q.x i) * q.x i)) -
        2 * (∑ i, mass i * D (q.y i) * q.y i) := by
      rw [coordinate_variation mass q.x (fun i => D (q.x i)) q.delta q.delta_symm,
        coordinate_variation mass q.y (fun i => D (q.y i)) q.delta q.delta_symm]
      simp_rw [← q.force_x, ← q.force_y]
    _ = _ := by
      rw [q.derivation_inertia D hm]
      simp only [Finset.sum_add_distrib]
      simp only [mul_assoc, mul_comm, mul_left_comm]
      ring

/-- The source's critical-value stationarity identity, stated over field
extensions so it can be used at a generic point, not just at complex points. -/
theorem derivation_potential_eq_zero (hm : ∀ i, D (mass i) = 0) :
    D q.potential = 0 := by
  have hD := congrArg D q.doubledPotential_eq
  have htwo : D (2 : K) = 0 := by simpa only [Nat.cast_ofNat] using D.map_natCast 2
  simp only [Derivation.leibniz, htwo, smul_eq_mul, mul_zero,
    add_zero, q.derivation_doubledPotential D hm] at hD
  have hthree : (3 : K) * D q.inertia = 0 := by linear_combination -hD
  have hi := (mul_eq_zero.mp hthree).resolve_left (by norm_num : (3 : K) ≠ 0)
  simpa only [q.potential_eq_inertia] using hi

theorem derivation_unorderedPotential_eq_zero (hm : ∀ i, D (mass i) = 0) :
    D q.unorderedPotential = 0 := by
  rw [← q.potential_eq_unordered]
  exact q.derivation_potential_eq_zero D hm

end NormalizedSystem
end CentralConfigurations
