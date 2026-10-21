import CentralConfigurations.Diagrams.BoundaryCuts

/-!
# Exact subsystem torque identities

These are the identities used in Albouy--Kaloshin (2012), Proposition 4,
which is Proposition 2.9 in Chang (2023). Every identity follows from the
two force equations with the existing symmetric inverse-distance witnesses.
-/

namespace CentralConfigurations

open scoped BigOperators

namespace ZWSystem

variable {K : Type*} [CommRing K] {n : ℕ} {mass : Fin n → K}

def torqueTerm (q : ZWSystem K n mass) (i j : Fin n) : K :=
  q.delta i j ^ 3 * (q.z i * q.w j - q.w i * q.z j)

theorem torqueTerm_antisymm (q : ZWSystem K n mass) (i j : Fin n) :
    q.torqueTerm i j = -q.torqueTerm j i := by
  simp only [torqueTerm, q.delta_symm i j]
  ring

theorem torque_row_zero (q : ZWSystem K n mass) (i : Fin n) :
    (∑ j, mass j * q.torqueTerm i j) = 0 := by
  calc
    _ = q.w i * (∑ j, mass j * q.delta i j ^ 3 * (q.z i - q.z j)) -
        q.z i * (∑ j, mass j * q.delta i j ^ 3 * (q.w i - q.w j)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      dsimp [torqueTerm]
      ring
    _ = 0 := by rw [← q.force_z i, ← q.force_w i]; ring

def torqueBalance (q : ZWSystem K n mass) : OneColorLimit K n mass where
  position := fun _ => 0
  force := q.torqueTerm
  diagonal i := by simp [torqueTerm, mul_comm]
  antisymm := q.torqueTerm_antisymm
  balance i := (q.torque_row_zero i).symm

theorem torque_boundary_zero [IsDomain K] [CharZero K]
    (q : ZWSystem K n mass) (s : Finset (Fin n)) :
    (∑ p ∈ s ×ˢ sᶜ, mass p.1 * mass p.2 * q.torqueTerm p.1 p.2) = 0 := by
  simpa [torqueBalance] using (q.torqueBalance.boundary_balance s).symm

theorem pair_torque_zero [IsDomain K] [CharZero K]
    (q : ZWSystem K n mass) (i j : Fin n) (hij : i ≠ j) :
    (∑ r ∈ ({i, j} : Finset (Fin n))ᶜ,
      (mass i * mass r * q.torqueTerm i r + mass j * mass r * q.torqueTerm j r)) = 0 := by
  have h := q.torque_boundary_zero {i, j}
  simpa only [Finset.sum_product, Finset.sum_pair hij, ← Finset.sum_add_distrib] using h

def torqueCorrection (q : ZWSystem K n mass) (i j : Fin n) : K :=
  q.delta i j ^ 2 * (q.z i * q.w j - q.w i * q.z j)

theorem torqueTerm_eq (q : ZWSystem K n mass) (i j : Fin n) :
    q.torqueTerm i j = q.delta i j * q.torqueCorrection i j := by
  dsimp [torqueTerm, torqueCorrection]
  ring

end ZWSystem

theorem ZWSystem.torqueCorrection_eq {K : Type*} [Field K] {n : ℕ}
    {mass : Fin n → K} (q : ZWSystem K n mass) (i j : Fin n) (hij : i ≠ j) :
    q.torqueCorrection i j =
      q.w i / (q.w i - q.w j) - q.z i / (q.z i - q.z j) := by
  have hz := q.z_separation_ne_zero hij
  have hw := q.w_separation_ne_zero hij
  have hid : (q.z i - q.z j) * (q.w i - q.w j) *
      (q.w i / (q.w i - q.w j) - q.z i / (q.z i - q.z j)) =
      q.z i * q.w j - q.w i * q.z j := by
    field_simp [hz, hw]
    ring
  rw [ZWSystem.torqueCorrection, ← hid, ← mul_assoc, q.distance i j hij, one_mul]

end CentralConfigurations
