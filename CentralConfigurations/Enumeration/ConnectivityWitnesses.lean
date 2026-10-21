import CentralConfigurations.Diagrams.MatrixReachability
import CentralConfigurations.Enumeration.MatrixFilters

/-!
# Connectivity certificates for the appendix pairing filter

The cut test implies positivity of the appendix's matrix sum. Finite
certificates therefore establish connectivity without repeated matrix-power
evaluation for each pair. Relabeling preserves the certified property.
-/

namespace CentralConfigurations

open scoped BigOperators

def ConnectedCuts {n : ℕ} (A : Fin n → Fin n → ℕ) : Prop :=
  ∀ s : Finset (Fin n), s.Nonempty → s ≠ Finset.univ →
    ∃ i ∈ s, ∃ j ∉ s, A i j ≠ 0

instance {n : ℕ} (A : Fin n → Fin n → ℕ) : Decidable (ConnectedCuts A) := by
  unfold ConnectedCuts
  infer_instance

theorem ConnectedCuts.reachable {n : ℕ} {A : Fin n → Fin n → ℕ}
    (h : ConnectedCuts A) (hs : ∀ i j, A i j = A j i) (i j : Fin n) :
    (offDiagonalGraph A hs).Reachable i j := by
  classical
  by_contra hn
  let s := ordinaryComponent A hs i
  have hne : s.Nonempty := ⟨i, (mem_ordinaryComponent A hs i i).mpr .rfl⟩
  have hj : j ∉ s := fun hh => hn ((mem_ordinaryComponent A hs i j).mp hh)
  have hproper : s ≠ Finset.univ := fun he => hj (he ▸ Finset.mem_univ j)
  obtain ⟨u, hu, v, hv, he⟩ := h s hne hproper
  exact he (ordinaryComponent_isolated A hs i u hu v hv)

theorem algorithmConnectivity_nonneg {n : ℕ} (A : Fin n → Fin n → ℕ) (i j : Fin n) :
    0 ≤ algorithmConnectivityMatrix A i j := by
  unfold algorithmConnectivityMatrix
  rw [Matrix.add_apply, Matrix.sum_apply]
  apply add_nonneg
  · simp only [Matrix.one_apply]; split_ifs <;> norm_num
  · exact Finset.sum_nonneg fun k _ => integerMatrix_pow_nonneg A k i j

theorem algorithmFullyConnected_of_reachable {n : ℕ} (A : Fin n → Fin n → ℕ)
    (hs : ∀ i j, A i j = A j i)
    (h : ∀ i j, (offDiagonalGraph A hs).Reachable i j) : AlgorithmFullyConnected A := by
  intro i j
  apply ne_of_gt
  by_cases hij : i = j
  · subst j
    have hn : 0 ≤ ∑ k ∈ Finset.Icc 1 (n - 1), (integerMatrix A ^ k) i i :=
      Finset.sum_nonneg fun k _ => integerMatrix_pow_nonneg A k i i
    simpa [algorithmConnectivityMatrix, integerMatrix, Matrix.add_apply,
      Matrix.sum_apply, Matrix.one_apply] using (show (0 : ℤ) < 1 +
        ∑ k ∈ Finset.Icc 1 (n - 1), (integerMatrix A ^ k) i i by omega)
  · obtain ⟨p, hp⟩ := (h i j).exists_isPath
    have hlen : p.length < n := by simpa using hp.length_lt
    have hpos : 0 < p.length := by
      cases p with
      | nil => exact (hij rfl).elim
      | cons => simp
    have hmem : p.length ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    have hsum := Finset.single_le_sum
      (fun k (_ : k ∈ Finset.Icc 1 (n - 1)) => integerMatrix_pow_nonneg A k i j) hmem
    have hstrict := (walk_integerMatrix_pow_pos A hs p).trans_le hsum
    simpa [algorithmConnectivityMatrix, integerMatrix, Matrix.add_apply,
      Matrix.sum_apply, Matrix.one_apply, hij] using hstrict

theorem ConnectedCuts.algorithmFullyConnected {n : ℕ} {A : Fin n → Fin n → ℕ}
    (h : ConnectedCuts A) (hs : ∀ i j, A i j = A j i) : AlgorithmFullyConnected A :=
  algorithmFullyConnected_of_reachable A hs (h.reachable hs)

theorem integerMatrix_pow_relabel {n : ℕ} (A : Fin n → Fin n → ℕ)
    (e : Equiv.Perm (Fin n)) (k : ℕ) (i j : Fin n) :
    (integerMatrix (fun u v => A (e u) (e v)) ^ k) i j =
      (integerMatrix A ^ k) (e i) (e j) := by
  induction k generalizing i j with
  | zero => simp [Matrix.one_apply, e.injective.eq_iff]
  | succ k ih =>
    simp only [pow_succ, Matrix.mul_apply, ih]
    exact Equiv.sum_comp e (fun r => (integerMatrix A ^ k) (e i) r * integerMatrix A r (e j))

theorem algorithmConnectivity_relabel {n : ℕ} (A : Fin n → Fin n → ℕ)
    (e : Equiv.Perm (Fin n)) (i j : Fin n) :
    algorithmConnectivityMatrix (fun u v => A (e u) (e v)) i j =
      algorithmConnectivityMatrix A (e i) (e j) := by
  simp only [algorithmConnectivityMatrix, Matrix.add_apply, Matrix.sum_apply]
  change (1 : Matrix (Fin n) (Fin n) ℤ) i j +
    ∑ k ∈ Finset.Icc 1 (n - 1), (integerMatrix (fun u v => A (e u) (e v)) ^ k) i j = _
  simp only [integerMatrix_pow_relabel, Matrix.one_apply, e.injective.eq_iff]
  rfl

theorem AlgorithmFullyConnected.relabel {n : ℕ} {A : Fin n → Fin n → ℕ}
    (h : AlgorithmFullyConnected A) (e : Equiv.Perm (Fin n)) :
    AlgorithmFullyConnected (fun u v => A (e u) (e v)) := by
  intro i j
  rw [algorithmConnectivity_relabel]
  exact h (e i) (e j)

end CentralConfigurations
