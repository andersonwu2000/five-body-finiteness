import CentralConfigurations.Model.ZW
import CentralConfigurations.Model.Virial
import Mathlib.Tactic

/-!
Exact five-body D9 potential bookkeeping.  The centered triple identity is
proved on the original force/metric system, before taking any limit.  In
particular its left side includes the complete residual triple potential.
Labels 0,1,2 form the triangle, 3,4 are the attached exterior vertices.
-/

namespace CentralConfigurations.FiveBody.D9

open scoped BigOperators

variable {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass)

def triplePotential : ℂ :=
  mass 0 * mass 1 * q.delta 0 1 + mass 0 * mass 2 * q.delta 0 2 +
  mass 1 * mass 2 * q.delta 1 2

def exteriorZ (i : Fin 5) : ℂ :=
  mass 3 * q.zForce i 3 + mass 4 * q.zForce i 4

def exteriorPotential : ℂ :=
  mass 0 * mass 3 * q.delta 0 3 + mass 0 * mass 4 * q.delta 0 4 +
  mass 1 * mass 3 * q.delta 1 3 + mass 1 * mass 4 * q.delta 1 4 +
  mass 2 * mass 3 * q.delta 2 3 + mass 2 * mass 4 * q.delta 2 4 +
  mass 3 * mass 4 * q.delta 3 4

theorem potential_decomposition :
    q.toNormalized.unorderedPotential = triplePotential q + exteriorPotential q := by
  simp [NormalizedSystem.unorderedPotential, ZWSystem.toNormalized,
    Fin.sum_univ_succ, triplePotential, exteriorPotential]
  ring

theorem force_z_split (i : Fin 5) :
    q.z i - exteriorZ q i =
      mass 0 * q.delta i 0 ^ 3 * (q.z i - q.z 0) +
      mass 1 * q.delta i 1 ^ 3 * (q.z i - q.z 1) +
      mass 2 * q.delta i 2 ^ 3 * (q.z i - q.z 2) := by
  have h := q.force_z i
  simp [Fin.sum_univ_succ] at h
  dsimp [exteriorZ, ZWSystem.zForce]
  linear_combination h

/-- The center may be arbitrary: internal force has zero weighted sum.
Choosing the exact triple w-center gives the centered virial in the report. -/
theorem centered_triple_virial (c : ℂ) :
    triplePotential q =
      mass 0 * (q.w 0 - c) * (q.z 0 - exteriorZ q 0) +
      mass 1 * (q.w 1 - c) * (q.z 1 - exteriorZ q 1) +
      mass 2 * (q.w 2 - c) * (q.z 2 - exteriorZ q 2) := by
  rw [force_z_split, force_z_split, force_z_split]
  simp only [q.delta_symm 1 0, q.delta_symm 2 0, q.delta_symm 2 1]
  have h01 := q.distance 0 1 (by decide)
  have h02 := q.distance 0 2 (by decide)
  have h12 := q.distance 1 2 (by decide)
  dsimp [triplePotential]
  linear_combination
    -(mass 0 * mass 1 * q.delta 0 1) * h01 -
    (mass 0 * mass 2 * q.delta 0 2) * h02 -
    (mass 1 * mass 2 * q.delta 1 2) * h12

theorem zForce_eq_delta_div_w (i j : Fin 5) (hij : i ≠ j) :
    q.zForce i j = q.delta i j / (q.w i - q.w j) := by
  apply (eq_div_iff (q.w_separation_ne_zero hij)).2
  have h := q.distance i j hij
  dsimp [ZWSystem.zForce]
  linear_combination q.delta i j * h

theorem outer_z_difference :
    (1 - (mass 3 + mass 4) * q.delta 3 4 ^ 3) * (q.z 3 - q.z 4) =
      (mass 0 * q.zForce 3 0 + mass 1 * q.zForce 3 1 + mass 2 * q.zForce 3 2) -
      (mass 0 * q.zForce 4 0 + mass 1 * q.zForce 4 1 + mass 2 * q.zForce 4 2) := by
  have h3 := q.force_z 3
  have h4 := q.force_z 4
  simp [Fin.sum_univ_succ] at h3 h4
  dsimp [ZWSystem.zForce]
  rw [q.delta_symm 4 3] at h4
  linear_combination h3 - h4

end CentralConfigurations.FiveBody.D9

