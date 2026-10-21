import CentralConfigurations.Diagrams.AppendixComponents
import Mathlib.Data.Finset.Prod

/-!
# The numerical connected-component filter in Appendix I

`RuleConnCompZQ/WQ` skips total traces and groups smaller than three, rejects
trace one, and rejects an all-circled group when every off-diagonal entry of
A+B is two. The source counts both orientations, hence the factor l(l-1).
This file proves the Boolean filter from the actual extracted solution limit.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

def componentDoubleCount {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℕ)
    (s : Finset (Fin n)) : ℕ :=
  (s.offDiag.filter (fun p => A p.1 p.2 + B p.1 p.2 = 2)).card

theorem componentDoubleCount_eq_iff {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℕ)
    (s : Finset (Fin n)) :
    componentDoubleCount A B s = s.card * (s.card - 1) ↔
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → A i j + B i j = 2 := by
  have hcard : s.offDiag.card = s.card * (s.card - 1) := by
    simp [Finset.offDiag_card, Nat.mul_sub_left_distrib]
  rw [componentDoubleCount, ← hcard, Finset.card_filter_eq_iff]
  constructor
  · intro h i hi j hj hij
    exact h (i, j) (Finset.mem_offDiag.mpr ⟨hi, hj, hij⟩)
  · intro h p hp
    have hh := Finset.mem_offDiag.mp hp
    exact h p.1 hh.1 p.2 hh.2.1 hh.2.2

theorem binary_trace_eq_card_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hb : ∀ i, A i i = 0 ∨ A i i = 1) (s : Finset (Fin n)) :
    (∑ i ∈ s, A i i) = s.card ↔ ∀ i ∈ s, A i i = 1 := by
  have hcount : (∑ i ∈ s, A i i) = (s.filter (fun i => A i i = 1)).card := by
    calc
      _ = ∑ i ∈ s, if A i i = 1 then (1 : ℕ) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        rcases hb i with h | h <;> simp [h]
      _ = _ := by simp only [Finset.sum_boole, Nat.cast_id]
  rw [hcount, Finset.card_filter_eq_iff]

theorem ComponentMatrixConclusion.count_ne_full {n : ℕ}
    {A B : Matrix (Fin n) (Fin n) ℕ} {s : Finset (Fin n)}
    (h : ComponentMatrixConclusion A B s) (hb : ∀ i, A i i = 0 ∨ A i i = 1)
    (hne : s.Nonempty) (ht : (∑ i ∈ s, A i i) = s.card) :
    componentDoubleCount A B s ≠ s.card * (s.card - 1) := by
  obtain ⟨i, hi, j, hj, hij, hd⟩ := h.2 hne ((binary_trace_eq_card_iff A hb s).mp ht)
  intro hc
  exact hd ((componentDoubleCount_eq_iff A B s).mp hc i hi j hj hij)

/-- Finite-set formulation of `RuleConnCompZQ` (swap A and B for WQ). -/
def appendixComponentCheck {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℕ) : Bool :=
  decide ((∑ i, A i i) < 3) || (appendixComponents A).all (fun s =>
    decide (s.card < 3) ||
      (decide ((∑ i ∈ s, A i i) ≠ 1) &&
        decide ((∑ i ∈ s, A i i) ≠ s.card ∨
          componentDoubleCount A B s ≠ s.card * (s.card - 1))))

theorem ScaledZWLimit.appendix_component_check {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass) :
    appendixComponentCheck l.z.matrix l.w.matrix = true := by
  unfold appendixComponentCheck
  rw [Bool.or_eq_true]
  right
  apply List.all_eq_true.mpr
  intro s hs
  by_cases hsmall : s.card < 3
  · simp [hsmall]
  · have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    have hc := l.appendix_component_matrix_rule ha hm s hs
    rw [Bool.or_eq_true]
    right
    rw [Bool.and_eq_true]
    constructor
    · simpa only [decide_eq_true_eq] using hc.1
    · simp only [decide_eq_true_eq]
      by_cases ht : (∑ i ∈ s, l.z.matrix i i) = s.card
      · exact Or.inr (hc.count_ne_full (fun i => l.z.matrix_binary i i) hne ht)
      · exact Or.inl ht

end CentralConfigurations
