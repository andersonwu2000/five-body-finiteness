import CentralConfigurations.Asymptotics.GaugeBounds

/-!
# Agreement with the thesis's upper-pair vector coordinates

The formal model stores both oriented force entries and diagonal zeroes. The
thesis's vector has only z_i and Z_ij for i<j (n(n+1)/2 entries). Opposite force
entries are negatives, so the sup norms agree exactly, not just up to a constant.
The upper-pair entry below uses the thesis's orientation Z_ij = delta^3(z_j-z_i).
-/

namespace CentralConfigurations

abbrev UpperPair (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev SourceCoordinate (n : ℕ) := Fin n ⊕ UpperPair n

theorem ZWSystem.zForce_antisymm {K : Type*} [CommRing K] {n : ℕ} {mass : Fin n → K}
    (q : ZWSystem K n mass) (i j : Fin n) : q.zForce i j = -q.zForce j i := by
  unfold zForce
  rw [q.delta_symm i j]
  ring

def ZWSystem.zSourceVector {n : ℕ} {mass : Fin n → ℂ} (q : ZWSystem ℂ n mass) :
    SourceCoordinate n → ℂ
  | .inl i => q.z i
  | .inr p => q.zForce p.val.2 p.val.1

def ZWSystem.wSourceVector {n : ℕ} {mass : Fin n → ℂ} (q : ZWSystem ℂ n mass) :
    SourceCoordinate n → ℂ := q.swap.zSourceVector

theorem ZWSystem.zVector_norm_eq_source {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) : ‖q.zVector‖ = ‖q.zSourceVector‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro c
    rcases c with i | ⟨i, j⟩
    · exact norm_le_pi_norm q.zSourceVector (.inl i)
    · change ‖q.zForce i j‖ ≤ _
      rcases lt_trichotomy i j with hij | hij | hij
      · rw [q.zForce_antisymm i j, norm_neg]
        exact norm_le_pi_norm q.zSourceVector (.inr ⟨(i, j), hij⟩)
      · subst j
        simp [zForce]
      · exact norm_le_pi_norm q.zSourceVector (.inr ⟨(j, i), hij⟩)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro c
    rcases c with i | ⟨⟨i, j⟩, _⟩
    · exact norm_le_pi_norm q.zVector (.inl i)
    · exact norm_le_pi_norm q.zVector (.inr (j, i))

theorem ZWSystem.wVector_norm_eq_source {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) : ‖q.wVector‖ = ‖q.wSourceVector‖ :=
  q.swap.zVector_norm_eq_source

end CentralConfigurations
