import CentralConfigurations.Diagrams.GraphComponents
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Paths, matrix powers, and circled vertices

The connectivity expressions in the source differ. Their component filters
can nevertheless be related to ordinary components through circled vertices:
a loop permits padding a simple path to every length at least n-1.
All matrices below are nonnegative, and all graph edges are off-diagonal.
-/

namespace CentralConfigurations

open scoped BigOperators

def integerMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) :
    Matrix (Fin n) (Fin n) ℤ := Matrix.of (fun i j => (A i j : ℤ))

def offDiagonalGraph {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) : SimpleGraph (Fin n) where
  Adj i j := i ≠ j ∧ A i j ≠ 0
  symm := by
    intro i j h
    exact ⟨h.1.symm, by rw [← hs i j]; exact h.2⟩
  loopless := ⟨fun i h => h.1 rfl⟩

noncomputable def ordinaryComponent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (i : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter ((offDiagonalGraph A hs).Reachable i)

@[simp] theorem mem_ordinaryComponent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (i j : Fin n) :
    j ∈ ordinaryComponent A hs i ↔ (offDiagonalGraph A hs).Reachable i j := by
  classical
  simp [ordinaryComponent]

theorem matrix_entry_reachable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (i j : Fin n) (h : A i j ≠ 0) :
    (offDiagonalGraph A hs).Reachable i j := by
  by_cases hij : i = j
  · subst j
    exact .rfl
  · exact SimpleGraph.Adj.reachable (G := offDiagonalGraph A hs) ⟨hij, h⟩

theorem ordinaryComponent_isolated {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (i : Fin n) :
    MatrixIsolated A (ordinaryComponent A hs i) := by
  intro j hj k hk
  by_contra he
  apply hk
  exact (mem_ordinaryComponent A hs i k).mpr
    (((mem_ordinaryComponent A hs i j).mp hj).trans (matrix_entry_reachable A hs j k he))

theorem integerMatrix_pow_nonneg {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (k : ℕ) (i j : Fin n) : 0 ≤ (integerMatrix A ^ k) i j := by
  induction k generalizing i j with
  | zero => simp [Matrix.one_apply]; split_ifs <;> norm_num
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg fun r _ => mul_nonneg (ih i r) (Int.natCast_nonneg _)

theorem integerMatrix_pow_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (k : ℕ) (i j : Fin n) :
    (integerMatrix A ^ k) i j = (integerMatrix A ^ k) j i := by
  have ht : (integerMatrix A).transpose = integerMatrix A := by
    ext u v
    change (A v u : ℤ) = (A u v : ℤ)
    rw [hs]
  have h := Matrix.transpose_pow (integerMatrix A) k
  rw [ht] at h
  exact congrArg (fun M => M j i) h

theorem integerMatrix_pow_reachable {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (k : ℕ) (i j : Fin n)
    (h : (integerMatrix A ^ k) i j ≠ 0) :
    (offDiagonalGraph A hs).Reachable i j := by
  induction k generalizing i j with
  | zero =>
      by_cases hij : i = j
      · subst j; exact .rfl
      · simp [hij] at h
  | succ k ih =>
      by_contra hn
      apply h
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro r _
      by_cases hr : (integerMatrix A ^ k) i r = 0
      · rw [hr, zero_mul]
      · by_cases he : A r j = 0
        · simp [integerMatrix, he]
        · exact (hn ((ih i r hr).trans (matrix_entry_reachable A hs r j he))).elim

theorem walk_integerMatrix_pow_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) {i j : Fin n}
    (p : (offDiagonalGraph A hs).Walk i j) :
    0 < (integerMatrix A ^ p.length) i j := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
      rw [SimpleGraph.Walk.length_cons, pow_succ', Matrix.mul_apply]
      have hv : (0 : ℤ) < integerMatrix A u v := by
        change (0 : ℤ) < (A u v : ℤ)
        exact_mod_cast Nat.pos_of_ne_zero h.2
      apply (mul_pos hv ih).trans_le
      exact Finset.single_le_sum
        (fun r _ => mul_nonneg (Int.natCast_nonneg _) (integerMatrix_pow_nonneg A p.length r w))
        (Finset.mem_univ v)

theorem integerMatrix_pow_le_of_loop {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (i j : Fin n) (hj : A j j = 1) {k r : ℕ} (hkr : k ≤ r) :
    (integerMatrix A ^ k) i j ≤ (integerMatrix A ^ r) i j := by
  induction r, hkr using Nat.le_induction with
  | base => rfl
  | succ r _ ih =>
      apply ih.trans
      rw [pow_succ, Matrix.mul_apply]
      have h := Finset.single_le_sum
        (fun v (_ : v ∈ Finset.univ) =>
          mul_nonneg (integerMatrix_pow_nonneg A r i v) (Int.natCast_nonneg (A v j)))
        (Finset.mem_univ j)
      simpa [integerMatrix, hj] using h

/-- A loop at the endpoint pads a simple path to the exponent used in the appendix. -/
theorem reachable_loop_power_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (i j : Fin n)
    (h : (offDiagonalGraph A hs).Reachable i j) (hj : A j j = 1)
    (k : ℕ) (hk : n - 1 ≤ k) : 0 < (integerMatrix A ^ k) i j := by
  obtain ⟨p, hp⟩ := h.exists_isPath
  have hlen : p.length < n := by simpa using hp.length_lt
  exact (walk_integerMatrix_pow_pos A hs p).trans_le
    (integerMatrix_pow_le_of_loop A i j hj (by omega))

/-- A circled vertex with a neighbor has at least two closed walks at every
length at least two: staying at the loop and making a two-step excursion. -/
theorem loop_neighbor_power_diagonal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (i j : Fin n) (hij : i ≠ j)
    (hi : A i i = 1) (he : A i j = 1) (k : ℕ) (hk : 2 ≤ k) :
    2 ≤ (integerMatrix A ^ k) i i := by
  have htwo : 2 ≤ (integerMatrix A ^ 2) i i := by
    rw [pow_two, Matrix.mul_apply]
    have h := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i, j} : Finset (Fin n)))
      (fun r _ _ => mul_nonneg (Int.natCast_nonneg (A i r)) (Int.natCast_nonneg (A r i)))
    simpa [Finset.sum_pair hij, integerMatrix, hi, hs j i, he] using h
  exact htwo.trans (integerMatrix_pow_le_of_loop A i i hi hk)

end CentralConfigurations
