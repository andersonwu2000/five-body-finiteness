import CentralConfigurations.Model.Normalized
import Mathlib.Tactic.LinearCombination

/-!
# The normalized virial identity U = I

Pairwise symmetrization gives the identity used before Chang's Lemma 2.2.
The doubled potential sums over ordered unequal pairs and counts each
unordered pair twice. PotentialFiniteness.lean uses this identity in the
proof of finite potential values.
-/

namespace CentralConfigurations

open scoped BigOperators

theorem double_sum_symmetrize {K : Type*} [CommRing K] {n : ℕ}
    (f : Fin n → Fin n → K) :
    (∑ i, ∑ j, (f i j + f j i)) = 2 * (∑ i, ∑ j, f i j) := by
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => f j i)]
  ring

/-- Pairwise symmetrization of a single coordinate of the force equation. -/
theorem coordinate_virial {K : Type*} [CommRing K] {n : ℕ}
    (mass pos : Fin n → K) (delta : Fin n → Fin n → K)
    (hs : ∀ i j, delta i j = delta j i) :
    (∑ i, ∑ j, mass i * mass j * delta i j ^ 3 * (pos i - pos j) ^ 2) =
      2 * (∑ i, mass i * pos i *
        (∑ j, mass j * delta i j ^ 3 * (pos i - pos j))) := by
  calc
    _ = ∑ i, ∑ j,
        (mass i * pos i * (mass j * delta i j ^ 3 * (pos i - pos j)) +
         mass j * pos j * (mass i * delta j i ^ 3 * (pos j - pos i))) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [hs j i]
      ring
    _ = 2 * (∑ i, ∑ j,
        mass i * pos i * (mass j * delta i j ^ 3 * (pos i - pos j))) :=
      double_sum_symmetrize _
    _ = _ := by simp only [Finset.mul_sum]

def NormalizedSystem.inertia {K : Type*} [CommRing K] {n : ℕ}
    {mass : Fin n → K} (q : NormalizedSystem K n mass) : K :=
  ∑ i, mass i * (q.x i ^ 2 + q.y i ^ 2)

def NormalizedSystem.doubledPotential {K : Type*} [CommRing K] {n : ℕ}
    {mass : Fin n → K} (q : NormalizedSystem K n mass) : K :=
  ∑ i, ∑ j, if i = j then 0 else mass i * mass j * q.delta i j

theorem NormalizedSystem.pair_virial {K : Type*} [CommRing K] {n : ℕ}
    {mass : Fin n → K} (q : NormalizedSystem K n mass) :
    (∑ i, ∑ j, mass i * mass j * q.delta i j ^ 3 * squaredSeparation q.x q.y i j) =
      2 * q.inertia := by
  simp only [squaredSeparation, mul_add, Finset.sum_add_distrib]
  rw [coordinate_virial mass q.x q.delta q.delta_symm,
    coordinate_virial mass q.y q.delta q.delta_symm]
  simp_rw [← q.force_x, ← q.force_y]
  unfold inertia
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem NormalizedSystem.potential_pair_identity {K : Type*} [CommRing K] {n : ℕ}
    {mass : Fin n → K} (q : NormalizedSystem K n mass) (i j : Fin n) :
    mass i * mass j * q.delta i j ^ 3 * squaredSeparation q.x q.y i j =
      if i = j then 0 else mass i * mass j * q.delta i j := by
  split_ifs with hij
  · subst j
    simp [squaredSeparation]
  · have hd := q.distance i j hij
    calc
      _ = mass i * mass j * q.delta i j *
          (q.delta i j ^ 2 * squaredSeparation q.x q.y i j) := by ring
      _ = _ := by rw [hd, mul_one]

theorem NormalizedSystem.doubledPotential_eq {K : Type*} [CommRing K] {n : ℕ}
    {mass : Fin n → K} (q : NormalizedSystem K n mass) :
    q.doubledPotential = 2 * q.inertia := by
  rw [← q.pair_virial]
  unfold doubledPotential
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (q.potential_pair_identity i j).symm

/-- The unordered-pair normalization, expressed as half the ordered-pair sum. -/
def NormalizedSystem.potential {K : Type*} [Field K] {n : ℕ}
    {mass : Fin n → K} (q : NormalizedSystem K n mass) : K :=
  q.doubledPotential / 2

/-- The thesis's original sum over pairs with i < j. -/
def NormalizedSystem.unorderedPotential {K : Type*} [CommRing K] {n : ℕ}
    {mass : Fin n → K} (q : NormalizedSystem K n mass) : K :=
  ∑ i, ∑ j, if i < j then mass i * mass j * q.delta i j else 0

theorem NormalizedSystem.ordered_eq_twice_unordered {K : Type*} [CommRing K]
    {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass) :
    q.doubledPotential = 2 * q.unorderedPotential := by
  unfold doubledPotential unorderedPotential
  rw [← double_sum_symmetrize
    (fun i j => if i < j then mass i * mass j * q.delta i j else 0)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [hij, ne_of_lt hij, not_lt_of_ge (le_of_lt hij)]
  · subst j
    simp
  · simp [hij, ne_of_gt hij, not_lt_of_ge (le_of_lt hij), q.delta_symm j i]
    ring

theorem NormalizedSystem.potential_eq_unordered {K : Type*} [Field K] [CharZero K]
    {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass) :
    q.potential = q.unorderedPotential := by
  unfold potential
  rw [q.ordered_eq_twice_unordered]
  ring

theorem NormalizedSystem.potential_eq_inertia {K : Type*} [Field K] [CharZero K]
    {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass) :
    q.potential = q.inertia := by
  unfold potential
  rw [q.doubledPotential_eq]
  ring

theorem NormalizedSystem.unorderedPotential_eq_inertia {K : Type*} [Field K] [CharZero K]
    {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass) :
    q.unorderedPotential = q.inertia :=
  q.potential_eq_unordered.symm.trans q.potential_eq_inertia

end CentralConfigurations
