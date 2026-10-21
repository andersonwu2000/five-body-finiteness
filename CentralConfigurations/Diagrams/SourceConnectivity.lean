import CentralConfigurations.Diagrams.ComponentRules
import Mathlib.Data.Matrix.Basic

/-!
# Source matrix powers and fully connected companions

Chang (2023), Definitions 3.2--3.3 and Theorem 3.7(a). The source uses
`A^(n+1) - I`, not a reflexive adjacency matrix. We retain that expression
over the integers, so subtraction on the diagonal has its literal meaning.
Full-ground-set positivity is automatically maximal among principal submatrices.
No equivalence with ordinary graph components is assumed here. SourceComponents
proves part 3.7(b) by retaining all circles of an ordinary component, without
requiring equality of the two vertex sets.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

/-- The literal integer matrix in Definition 3.2. -/
def sourceConnectivityMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) :
    Matrix (Fin n) (Fin n) ℤ :=
  (Matrix.of (fun i j => (A i j : ℤ))) ^ (n + 1) - 1

/-- Positivity of a principal submatrix in the source's definition. -/
def SourcePrincipalPositive {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (s : Finset (Fin n)) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, 0 < sourceConnectivityMatrix A i j

/-- Definition 3.3: positivity on the entire ground set. Maximality is automatic. -/
def SourceFullyConnected {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  SourcePrincipalPositive A Finset.univ

theorem source_full_principal_maximal {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (h : SourceFullyConnected A) :
    SourcePrincipalPositive A Finset.univ ∧
      ∀ t : Finset (Fin n), Finset.univ ⊆ t → SourcePrincipalPositive A t →
        t = Finset.univ := by
  exact ⟨h, fun t ht _ => Finset.Subset.antisymm (Finset.subset_univ t) ht⟩

/-- If nonzero matrix entries preserve a label, all powers preserve that label.
This is a direct finite-sum argument, without a graph-connectivity assumption. -/
theorem matrix_pow_preserves_labels {n : ℕ} {α : Type*}
    (A : Matrix (Fin n) (Fin n) ℤ) (p : Fin n → α)
    (hA : ∀ i j, A i j ≠ 0 → p i = p j) (k : ℕ) :
    ∀ i j, (A ^ k) i j ≠ 0 → p i = p j := by
  induction k with
  | zero =>
      intro i j hij
      by_contra h
      have hne : i ≠ j := fun e => h (congrArg p e)
      simp [hne] at hij
  | succ k ih =>
      intro i j hij
      by_contra h
      apply hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro r _
      by_cases hir : (A ^ k) i r = 0
      · rw [hir, zero_mul]
      · by_cases hrj : A r j = 0
        · rw [hrj, mul_zero]
        · exact (h ((ih i r hir).trans (hA r j hrj))).elim

theorem SourcePrincipalPositive.power_nonzero {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℕ} {s : Finset (Fin n)}
    (h : SourcePrincipalPositive A s) (i : Fin n) (hi : i ∈ s)
    (j : Fin n) (hj : j ∈ s) :
    ((Matrix.of (fun u v => (A u v : ℤ))) ^ (n + 1)) i j ≠ 0 := by
  intro hz
  have hp := h i hi j hj
  simp only [sourceConnectivityMatrix, Matrix.sub_apply, hz, Matrix.one_apply] at hp
  split_ifs at hp <;> norm_num at hp

theorem ScaledZWLimit.z_power_w_close {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (k : ℕ) (i j : Fin n)
    (h : ((Matrix.of (fun u v => (l.z.matrix u v : ℤ))) ^ k) i j ≠ 0) :
    l.w.position i = l.w.position j := by
  apply matrix_pow_preserves_labels (fun u v => (l.z.matrix u v : ℤ)) l.w.position
    _ k i j h
  intro u v huv
  by_cases heq : u = v
  · exact congrArg l.w.position heq
  · apply l.z_stroke_w_close ha u v heq
    intro hf
    simp [OneColorLimit.matrix, OneColorLimit.Incident, heq, hf] at huv

/-- Theorem 3.7(a), with the original power-minus-identity definition. -/
theorem ScaledZWLimit.source_fully_connected_w_positions_zero {n : ℕ}
    {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ}
    (l : ScaledZWLimit q a) (ha : Tendsto a atTop (𝓝 0))
    (hm : AdmissibleMasses mass) (hc : SourceFullyConnected l.z.matrix) :
    ∀ i, l.w.position i = 0 := by
  intro i
  apply l.w.coincident_component_circles_zero hm Finset.univ i (Finset.mem_univ i)
  · intro j _ k hk
    exact (hk (Finset.mem_univ k)).elim
  · intro j _ _
    exact l.z_power_w_close ha (n + 1) j i
      (hc.power_nonzero j (Finset.mem_univ j) i (Finset.mem_univ i))

def FullyConnectedCompanionRule {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  SourceFullyConnected A → (∑ i, B i i) = 0

theorem ScaledZWLimit.source_fully_connected_companion_trace {n : ℕ}
    {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ}
    (l : ScaledZWLimit q a) (ha : Tendsto a atTop (𝓝 0))
    (hm : AdmissibleMasses mass) : FullyConnectedCompanionRule l.z.matrix l.w.matrix := by
  intro hc
  have hw := l.source_fully_connected_w_positions_zero ha hm hc
  classical
  simp [OneColorLimit.matrix, OneColorLimit.Incident, hw]

end CentralConfigurations
