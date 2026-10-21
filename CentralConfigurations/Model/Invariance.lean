import CentralConfigurations.Model.Normalized
import Mathlib.Data.Complex.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Mass hypotheses, scalar extension, and simultaneous relabeling

These operations connect the physical real system to the complex system and
support the common permutation of both diagram colors used in Algorithm I.
No independent canonicalization of the two colors is licensed here.
-/

namespace CentralConfigurations

open scoped BigOperators

def AdmissibleMasses {K : Type*} [AddCommMonoid K] {n : ℕ} (mass : Fin n → K) : Prop :=
  ∀ s : Finset (Fin n), s.Nonempty → ∑ i ∈ s, mass i ≠ 0

/-- Positive real masses satisfy the nonzero-subsystem hypothesis on page 5. -/
theorem positive_masses_admissible {n : ℕ} (mass : Fin n → ℝ)
    (hpos : ∀ i, 0 < mass i) : AdmissibleMasses mass := by
  intro s hs
  exact ne_of_gt (Finset.sum_pos (fun i _ => hpos i) hs)

theorem complex_positive_masses_admissible {n : ℕ} (mass : Fin n → ℝ)
    (hpos : ∀ i, 0 < mass i) : AdmissibleMasses (fun i => (mass i : ℂ)) := by
  intro s hs hz
  apply positive_masses_admissible mass hpos s hs
  have hr := congrArg Complex.re hz
  simpa using hr

/-- Every ring homomorphism transports the complete polynomial system. -/
def NormalizedSystem.map {K L : Type*} [CommRing K] [CommRing L]
    {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass) (f : K →+* L) :
    NormalizedSystem L n (fun i => f (mass i)) where
  x i := f (q.x i)
  y i := f (q.y i)
  delta i j := f (q.delta i j)
  delta_symm i j := congrArg f (q.delta_symm i j)
  delta_diagonal i := by rw [q.delta_diagonal, map_zero]
  force_x i := by simpa using congrArg f (q.force_x i)
  force_y i := by simpa using congrArg f (q.force_y i)
  distance i j hij := by
    simpa [squaredSeparation] using congrArg f (q.distance i j hij)

/-- The same permutation must act on positions, masses, and all pair variables. -/
def NormalizedSystem.relabel {K : Type*} [CommRing K] {n : ℕ}
    {mass : Fin n → K} (q : NormalizedSystem K n mass) (e : Fin n ≃ Fin n) :
    NormalizedSystem K n (fun i => mass (e i)) where
  x i := q.x (e i)
  y i := q.y (e i)
  delta i j := q.delta (e i) (e j)
  delta_symm i j := q.delta_symm (e i) (e j)
  delta_diagonal i := q.delta_diagonal (e i)
  force_x i := by
    calc
      _ = ∑ k, mass k * q.delta (e i) k ^ 3 * (q.x (e i) - q.x k) := q.force_x (e i)
      _ = _ := (e.sum_comp _).symm
  force_y i := by
    calc
      _ = ∑ k, mass k * q.delta (e i) k ^ 3 * (q.y (e i) - q.y k) := q.force_y (e i)
      _ = _ := (e.sum_comp _).symm
  distance i j hij := q.distance (e i) (e j) (fun h => hij (e.injective h))

end CentralConfigurations
