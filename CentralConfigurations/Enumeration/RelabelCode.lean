import CentralConfigurations.Enumeration.BinaryMatrices

namespace CentralConfigurations

/-- The forward map suffices for computing a relabeled binary code. -/
def rawRelabel {n : ℕ} (c : BinaryMatrixCode n) (e : Fin n → Fin n) : BinaryMatrixCode n :=
  fun p => c (upperIndex (e p.1.1) (e p.1.2))

theorem rawRelabel_eq_relabel {n : ℕ} (c : BinaryMatrixCode n) (e : Equiv.Perm (Fin n)) :
    rawRelabel c e = BinaryMatrixCode.relabel c e := by
  funext p
  change c (upperIndex (e p.1.1) (e p.1.2)) =
    decide ((if c (upperIndex (e p.1.1) (e p.1.2)) then 1 else 0) = 1)
  exact (show ∀ b : Bool, b = decide ((if b then (1 : ℕ) else 0) = 1) by
    intro b; cases b <;> rfl) _

end CentralConfigurations
