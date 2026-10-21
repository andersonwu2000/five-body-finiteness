import CentralConfigurations.Model.ZW

/-!
# Mass-center identities in the branch-free z/w model

These are the algebraic identities used in Proposition 4.7(b). They follow
from the force equations and hold over every characteristic-zero domain.
-/

namespace CentralConfigurations

open scoped BigOperators

variable {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
variable {n : ℕ} {mass : Fin n → K}

theorem ZWSystem.mass_center_z (q : ZWSystem K n mass) :
    ∑ i, mass i * q.z i = 0 := by
  calc
    _ = ∑ i, mass i * (∑ j, mass j * q.delta i j ^ 3 * (q.z i - q.z j)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← q.force_z i]
    _ = 0 := weighted_force_sum_zero mass q.z q.delta q.delta_symm

theorem ZWSystem.mass_center_w (q : ZWSystem K n mass) :
    ∑ i, mass i * q.w i = 0 := q.swap.mass_center_z

theorem ZWSystem.mass_separation_sum_z (q : ZWSystem K n mass) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, mass j * (q.z i - q.z j) = (∑ j, mass j) * q.z i := by
  calc
    _ = ∑ j, mass j * (q.z i - q.z j) := by
      simpa using (Finset.sum_erase_add (s := Finset.univ)
        (f := fun j => mass j * (q.z i - q.z j)) (Finset.mem_univ i))
    _ = (∑ j, mass j) * q.z i - ∑ j, mass j * q.z j := by
      simp only [mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]
    _ = _ := by rw [q.mass_center_z, sub_zero]

theorem ZWSystem.mass_separation_sum_w (q : ZWSystem K n mass) (i : Fin n) :
    ∑ j ∈ Finset.univ.erase i, mass j * (q.w i - q.w j) = (∑ j, mass j) * q.w i :=
  q.swap.mass_separation_sum_z i

end CentralConfigurations
