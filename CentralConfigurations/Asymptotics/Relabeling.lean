import CentralConfigurations.Diagrams.MatrixRules

/-!
# Relabeling actual solutions and their common-scale limits

Algorithm I may sort one diagonal only when the same permutation transports
both colors and the masses. Finite sup norms, hence the canonical inverse
scale, are unchanged. This lets necessary conditions be reapplied to actual
relabeled solutions, including the order-dependent appendix component test.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

def ZWSystem.relabel {K : Type*} [CommRing K] {n : ℕ} {mass : Fin n → K}
    (q : ZWSystem K n mass) (e : Equiv.Perm (Fin n)) :
    ZWSystem K n (fun i => mass (e i)) where
  z i := q.z (e i)
  w i := q.w (e i)
  delta i j := q.delta (e i) (e j)
  delta_symm i j := q.delta_symm (e i) (e j)
  delta_diagonal i := q.delta_diagonal (e i)
  force_z i := by
    calc
      _ = ∑ k, mass k * q.delta (e i) k ^ 3 * (q.z (e i) - q.z k) := q.force_z (e i)
      _ = _ := (Equiv.sum_comp e
        (fun k => mass k * q.delta (e i) k ^ 3 * (q.z (e i) - q.z k))).symm
  force_w i := by
    calc
      _ = ∑ k, mass k * q.delta (e i) k ^ 3 * (q.w (e i) - q.w k) := q.force_w (e i)
      _ = _ := (Equiv.sum_comp e
        (fun k => mass k * q.delta (e i) k ^ 3 * (q.w (e i) - q.w k))).symm
  distance i j hij := q.distance (e i) (e j) (fun h => hij (e.injective h))

def OneColorLimit.relabel {K : Type*} [CommRing K] {n : ℕ} {mass : Fin n → K}
    (l : OneColorLimit K n mass) (e : Equiv.Perm (Fin n)) :
    OneColorLimit K n (fun i => mass (e i)) where
  position i := l.position (e i)
  force i j := l.force (e i) (e j)
  diagonal i := l.diagonal (e i)
  antisymm i j := l.antisymm (e i) (e j)
  balance i := by
    rw [l.balance (e i)]
    exact (Equiv.sum_comp e (fun k => mass k * l.force (e i) k)).symm

theorem finite_complex_norm_comp {ι κ : Type*} [Fintype ι] [Fintype κ]
    (v : κ → ℂ) (e : ι ≃ κ) : ‖fun i => v (e i)‖ = ‖v‖ := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    exact norm_le_pi_norm v (e i)
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro k
    obtain ⟨i, rfl⟩ := e.surjective k
    exact norm_le_pi_norm (fun i => v (e i)) i

def colorCoordinateRelabel {n : ℕ} (e : Equiv.Perm (Fin n)) :
    Equiv.Perm (ColorCoordinate n) := Equiv.sumCongr e (Equiv.prodCongr e e)

theorem ZWSystem.zVector_relabel {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (e : Equiv.Perm (Fin n)) :
    (q.relabel e).zVector = fun c => q.zVector (colorCoordinateRelabel e c) := by
  funext c
  rcases c with i | ⟨i, j⟩ <;> rfl

theorem ZWSystem.wVector_relabel {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (e : Equiv.Perm (Fin n)) :
    (q.relabel e).wVector = fun c => q.wVector (colorCoordinateRelabel e c) := by
  funext c
  rcases c with i | ⟨i, j⟩ <;> rfl

@[simp] theorem ZWSystem.zVector_norm_relabel {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (e : Equiv.Perm (Fin n)) :
    ‖(q.relabel e).zVector‖ = ‖q.zVector‖ := by
  rw [q.zVector_relabel]
  exact finite_complex_norm_comp _ _

@[simp] theorem ZWSystem.wVector_norm_relabel {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (e : Equiv.Perm (Fin n)) :
    ‖(q.relabel e).wVector‖ = ‖q.wVector‖ := by
  rw [q.wVector_relabel]
  exact finite_complex_norm_comp _ _

@[simp] theorem ZWSystem.inverseScale_relabel {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (e : Equiv.Perm (Fin n)) :
    (q.relabel e).inverseScale = q.inverseScale := by
  simp only [inverseScale, zVector_norm_relabel]

theorem OneColorLimit.nonzero_relabel_iff {n : ℕ} {mass : Fin n → ℂ}
    (l : OneColorLimit ℂ n mass) (e : Equiv.Perm (Fin n)) :
    (l.relabel e).Nonzero ↔ l.Nonzero := by
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, j, hij⟩)
    · exact Or.inl ⟨e i, hi⟩
    · exact Or.inr ⟨e i, e j, hij⟩
  · rintro (⟨i, hi⟩ | ⟨i, j, hij⟩)
    · exact Or.inl ⟨e.symm i, by simpa [relabel] using hi⟩
    · exact Or.inr ⟨e.symm i, e.symm j, by simpa [relabel] using hij⟩

theorem OneColorLimit.matrix_relabel {n : ℕ} {mass : Fin n → ℂ}
    (l : OneColorLimit ℂ n mass) (e : Equiv.Perm (Fin n)) :
    (l.relabel e).matrix = fun i j => l.matrix (e i) (e j) := by
  funext i j
  simp only [matrix, Incident, e.injective.eq_iff, relabel]

def ScaledZWLimit.relabel {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (e : Equiv.Perm (Fin n)) : ScaledZWLimit (fun t => (q t).relabel e) a where
  z := l.z.relabel e
  w := l.w.relabel e
  z_position i := l.z_position (e i)
  w_position i := l.w_position (e i)
  z_force i j := l.z_force (e i) (e j)
  w_force i j := l.w_force (e i) (e j)

def ScaledZWLimit.relabelCanonical {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (e : Equiv.Perm (Fin n)) :
    ScaledZWLimit (fun t => (q t).relabel e) (fun t => ((q t).relabel e).inverseScale) where
  z := l.z.relabel e
  w := l.w.relabel e
  z_position i := by
    simpa only [ZWSystem.inverseScale_relabel] using (l.relabel e).z_position i
  w_position i := by
    simpa only [ZWSystem.inverseScale_relabel] using (l.relabel e).w_position i
  z_force i j := by
    simpa only [ZWSystem.inverseScale_relabel] using (l.relabel e).z_force i j
  w_force i j := by
    simpa only [ZWSystem.inverseScale_relabel] using (l.relabel e).w_force i j

end CentralConfigurations
