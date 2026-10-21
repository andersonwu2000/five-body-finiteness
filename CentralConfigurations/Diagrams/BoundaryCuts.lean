import CentralConfigurations.Diagrams.MatrixRules
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Trace-zero cuts cannot have exactly one stroke

Chang (2023), Theorem 3.8. This rule is essential to the six-body enumeration.
The finite boundary-flow identity is proved first for every one-color limit;
the numerical matrix rule is then derived from its exact nonzero support.
-/

namespace CentralConfigurations

open scoped BigOperators

namespace OneColorLimit

theorem boundary_balance {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    {n : ℕ} {mass : Fin n → K} (q : OneColorLimit K n mass) (s : Finset (Fin n)) :
    (∑ i ∈ s, mass i * q.position i) =
      ∑ p ∈ s ×ˢ sᶜ, mass p.1 * mass p.2 * q.force p.1 p.2 := by
  classical
  have hinside : (∑ i ∈ s, ∑ j ∈ s, mass i * mass j * q.force i j) = 0 :=
    antisymmetric_sum_zero s _ (by intro i _ j _; rw [q.antisymm i j]; ring)
  calc
    _ = (∑ i ∈ s, ∑ j ∈ s, mass i * mass j * q.force i j) +
        (∑ i ∈ s, ∑ j ∈ sᶜ, mass i * mass j * q.force i j) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [q.balance i, Finset.mul_sum]
      simp only [← mul_assoc]
      exact (Finset.sum_add_sum_compl s (fun j => mass i * mass j * q.force i j)).symm
    _ = _ := by rw [hinside, zero_add, Finset.sum_product]

variable {n : ℕ} {mass : Fin n → ℂ}

noncomputable def boundarySupport (q : OneColorLimit ℂ n mass) (s : Finset (Fin n)) :
    Finset (Fin n × Fin n) := by
  classical
  exact (s ×ˢ sᶜ).filter (fun p => q.force p.1 p.2 ≠ 0)

theorem boundary_balance_on_support (q : OneColorLimit ℂ n mass) (s : Finset (Fin n)) :
    (∑ i ∈ s, mass i * q.position i) =
      ∑ p ∈ q.boundarySupport s, mass p.1 * mass p.2 * q.force p.1 p.2 := by
  rw [q.boundary_balance s]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hps
  have hz : q.force p.1 p.2 = 0 := by
    by_contra h
    exact hps (Finset.mem_filter.mpr ⟨hp, h⟩)
  rw [hz, mul_zero]

theorem boundarySupport_card_ne_one (q : OneColorLimit ℂ n mass) (hm : ∀ i, mass i ≠ 0)
    (s : Finset (Fin n)) (hzero : ∀ i ∈ s, q.position i = 0) :
    (q.boundarySupport s).card ≠ 1 := by
  classical
  intro hc
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hc
  have hmem : p ∈ q.boundarySupport s := by rw [hp]; simp
  have hf : q.force p.1 p.2 ≠ 0 := (Finset.mem_filter.mp hmem).2
  have hbalance := q.boundary_balance_on_support s
  rw [hp, Finset.sum_singleton] at hbalance
  have hz : (∑ i ∈ s, mass i * q.position i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i hi, mul_zero]
  rw [hz] at hbalance
  exact mul_ne_zero (mul_ne_zero (hm p.1) (hm p.2)) hf hbalance.symm

theorem cut_sum_eq_boundarySupport_card (q : OneColorLimit ℂ n mass) (s : Finset (Fin n)) :
    (∑ i ∈ s, ∑ j ∈ sᶜ, q.matrix i j) = (q.boundarySupport s).card := by
  classical
  calc
    _ = ∑ p ∈ s ×ˢ sᶜ, q.matrix p.1 p.2 := (Finset.sum_product _ _ _).symm
    _ = ∑ p ∈ s ×ˢ sᶜ, if q.force p.1 p.2 ≠ 0 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      have hm := Finset.mem_product.mp hp
      have hne : p.1 ≠ p.2 := by
        intro heq
        exact (Finset.mem_compl.mp hm.2) (heq ▸ hm.1)
      simp [matrix, Incident, hne]
    _ = _ := Finset.sum_boole (fun p : Fin n × Fin n => q.force p.1 p.2 ≠ 0) (s ×ˢ sᶜ)

/-- Theorem 3.8 for either single-color leading matrix. -/
theorem trace_zero_cut_ne_one (q : OneColorLimit ℂ n mass) (hm : ∀ i, mass i ≠ 0)
    (s : Finset (Fin n)) (hzero : ∀ i ∈ s, q.matrix i i = 0) :
    (∑ i ∈ s, ∑ j ∈ sᶜ, q.matrix i j) ≠ 1 := by
  rw [q.cut_sum_eq_boundarySupport_card s]
  apply q.boundarySupport_card_ne_one hm s
  intro i hi
  simpa [matrix, Incident] using hzero i hi

end OneColorLimit

def TraceZeroCutRule {n : ℕ} (A : Fin n → Fin n → ℕ) : Prop :=
  ∀ s : Finset (Fin n), (∀ i ∈ s, A i i = 0) → (∑ i ∈ s, ∑ j ∈ sᶜ, A i j) ≠ 1

end CentralConfigurations
