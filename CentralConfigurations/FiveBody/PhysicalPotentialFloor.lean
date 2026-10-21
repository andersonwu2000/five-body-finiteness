import CentralConfigurations.Model.FixedPotentialLevel
import CentralConfigurations.Asymptotics.FourProductAlgebra
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Physical numerical potential floor

Two Cauchy inequalities prove the weighted cubic bound. The exact centered
pair-inertia identity and normalized virial then give S³ ≤ M I₀³.
This theorem is only about a real positive-sheet normalized point. The scalar
can subsequently be transported to a complex affine potential level.
-/

namespace CentralConfigurations
noncomputable section
open scoped BigOperators

def totalMass {n : ℕ} (mass : Fin n → ℝ) : ℝ := ∑ i, mass i

def pairMassSum {n : ℕ} (mass : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, if i < j then mass i * mass j else 0

def PhysicalPotentialLevel {n : ℕ} (mass : Fin n → ℝ) (c : ℝ) : Prop :=
  0 < c ∧ pairMassSum mass ^ 3 ≤ totalMass mass * c ^ 3

theorem weighted_inverse_cubic {ι : Type*} [Fintype ι]
    (w d : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hd : ∀ i, 0 < d i)
    (hS : 0 < ∑ i, w i) :
    (∑ i, w i) ^ 3 ≤ (∑ i, w i / d i ^ 2) * (∑ i, w i * d i) ^ 2 := by
  have h1 : (∑ i, w i) ^ 2 ≤ (∑ i, w i * d i) * ∑ i, w i / d i := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (fun i _ => mul_nonneg (hw i) (hd i).le)
      (fun i _ => div_nonneg (hw i) (hd i).le)
    intro i _
    field_simp [ne_of_gt (hd i)]
  have h2 : (∑ i, w i / d i) ^ 2 ≤ (∑ i, w i) * ∑ i, w i / d i ^ 2 := by
    apply Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
      (fun i _ => hw i)
      (fun i _ => div_nonneg (hw i) (sq_nonneg _))
    intro i _
    ring
  have h4 : (∑ i, w i) * (∑ i, w i) ^ 3 ≤
      (∑ i, w i) * ((∑ i, w i / d i ^ 2) * (∑ i, w i * d i) ^ 2) := by
    calc
      _ = ((∑ i, w i) ^ 2) ^ 2 := by ring
      _ ≤ ((∑ i, w i * d i) * ∑ i, w i / d i) ^ 2 :=
        pow_le_pow_left₀ (sq_nonneg _) h1 2
      _ = (∑ i, w i * d i) ^ 2 * (∑ i, w i / d i) ^ 2 := by ring
      _ ≤ (∑ i, w i * d i) ^ 2 * ((∑ i, w i) * ∑ i, w i / d i ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  exact le_of_mul_le_mul_of_pos_left h4 hS

def fiveBodyPairWeight (mass : Fin 5 → ℝ) (e : Fin 10) : ℝ :=
  mass (fiveBodyEdges e).1 * mass (fiveBodyEdges e).2

theorem five_body_pairMassSum (mass : Fin 5 → ℝ) :
    pairMassSum mass = ∑ e, fiveBodyPairWeight mass e := by
  simp [pairMassSum, fiveBodyPairWeight, fiveBodyEdges, Fin.sum_univ_succ]
  ring

theorem NormalizedSystem.five_body_potential_edge_sum {mass : Fin 5 → ℝ}
    (q : NormalizedSystem ℝ 5 mass) :
    q.unorderedPotential = ∑ e, fiveBodyPairWeight mass e *
      q.delta (fiveBodyEdges e).1 (fiveBodyEdges e).2 := by
  simp [NormalizedSystem.unorderedPotential, fiveBodyPairWeight, fiveBodyEdges,
    Fin.sum_univ_succ]
  ring

theorem five_body_pair_inertia_identity (mass x y : Fin 5 → ℝ) :
    (∑ e, fiveBodyPairWeight mass e *
      squaredSeparation x y (fiveBodyEdges e).1 (fiveBodyEdges e).2) =
      totalMass mass * (∑ i, mass i * (x i ^ 2 + y i ^ 2)) -
        (∑ i, mass i * x i) ^ 2 - (∑ i, mass i * y i) ^ 2 := by
  simp [fiveBodyPairWeight, fiveBodyEdges, squaredSeparation, totalMass,
    Fin.sum_univ_succ]
  ring

theorem NormalizedSystem.five_body_pair_inertia {mass : Fin 5 → ℝ}
    (q : NormalizedSystem ℝ 5 mass) :
    (∑ e, fiveBodyPairWeight mass e *
      squaredSeparation q.x q.y (fiveBodyEdges e).1 (fiveBodyEdges e).2) =
      totalMass mass * q.inertia := by
  rw [five_body_pair_inertia_identity, q.mass_center_x, q.mass_center_y]
  simp [NormalizedSystem.inertia]

theorem NormalizedSystem.physicalPotentialLevel {mass : Fin 5 → ℝ}
    (q : NormalizedSystem ℝ 5 mass) (hm : ∀ i, 0 < mass i)
    (hdelta : ∀ i j, i ≠ j → 0 < q.delta i j) :
    PhysicalPotentialLevel mass q.unorderedPotential := by
  let w := fiveBodyPairWeight mass
  let d := fun e => q.delta (fiveBodyEdges e).1 (fiveBodyEdges e).2
  have hw (e : Fin 10) : 0 < w e := mul_pos (hm _) (hm _)
  have hd (e : Fin 10) : 0 < d e := hdelta _ _ (five_body_edge_distinct e)
  have hS : 0 < ∑ e, w e := Finset.sum_pos (fun e _ => hw e) Finset.univ_nonempty
  have hU : 0 < ∑ e, w e * d e :=
    Finset.sum_pos (fun e _ => mul_pos (hw e) (hd e)) Finset.univ_nonempty
  have hD : (∑ e, w e / d e ^ 2) = totalMass mass * q.inertia := by
    rw [← q.five_body_pair_inertia]
    apply Finset.sum_congr rfl
    intro e _
    apply (div_eq_iff (ne_of_gt (pow_pos (hd e) 2))).mpr
    have h := q.distance _ _ (five_body_edge_distinct e)
    dsimp [w, d]
    calc
      _ = fiveBodyPairWeight mass e *
          (q.delta (fiveBodyEdges e).1 (fiveBodyEdges e).2 ^ 2 *
            squaredSeparation q.x q.y (fiveBodyEdges e).1 (fiveBodyEdges e).2) := by
        rw [h, mul_one]
      _ = _ := by ring
  have hfloor := weighted_inverse_cubic w d (fun e => (hw e).le) hd hS
  rw [hD, ← q.five_body_potential_edge_sum, q.unorderedPotential_eq_inertia] at hfloor
  constructor
  · simpa only [w, d, ← q.five_body_potential_edge_sum] using hU
  · dsimp [PhysicalPotentialLevel]
    rw [five_body_pairMassSum]
    change (∑ e, w e) ^ 3 ≤ totalMass mass * q.unorderedPotential ^ 3
    rw [q.unorderedPotential_eq_inertia]
    nlinarith [hfloor]

end
end CentralConfigurations
