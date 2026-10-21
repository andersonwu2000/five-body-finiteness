import CentralConfigurations.Enumeration.OrderDomains
import Mathlib.Data.Fintype.BigOperators

/-!
# The product-count stopping test in Appendix II

The count is exactly the number of singleton completions of a box.
Under refinement, equal positive counts force equal boxes. At count zero
the box may still change, but it admits no assignment and can be discarded.
The recursive implementation uses the source's count-equality stopping test.
-/

namespace CentralConfigurations
namespace OrderBox

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def completions (B : OrderBox ι) : Finset (ι → Fin 6) := Fintype.piFinset B

def completionCount (B : OrderBox ι) : ℕ := ∏ i, (B i).card

theorem mem_completions (B : OrderBox ι) (k : ι → Fin 6) :
    k ∈ completions B ↔ B.Admits k := Fintype.mem_piFinset

theorem completions_card (B : OrderBox ι) :
    (completions B).card = completionCount B := Fintype.card_piFinset B

theorem completionCount_pos_iff (B : OrderBox ι) :
    0 < completionCount B ↔ ∀ i, (B i).Nonempty := by
  rw [← completions_card,Finset.card_pos]
  exact Fintype.piFinset_nonempty

theorem completionCount_zero_iff (B : OrderBox ι) :
    completionCount B = 0 ↔ ¬ ∃ k, B.Admits k := by
  rw [← completions_card,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
  simp only [mem_completions,not_exists]

theorem Admits.completionCount_pos {B : OrderBox ι} {k : ι → Fin 6}
    (h : B.Admits k) : 0 < completionCount B :=
  (completionCount_pos_iff B).mpr (fun i => ⟨k i,h i⟩)

omit [Fintype ι] [DecidableEq ι] in
theorem Refines.trans {A B C : OrderBox ι} (hAB : A.Refines B) (hBC : B.Refines C) :
    A.Refines C := fun i => (hAB i).trans (hBC i)

theorem Refines.completions_subset {A B : OrderBox ι} (h : A.Refines B) :
    completions A ⊆ completions B := Fintype.piFinset_subset A B h

omit [DecidableEq ι] in
theorem Refines.completionCount_le {A B : OrderBox ι} (h : A.Refines B) :
    completionCount A ≤ completionCount B :=
  Finset.prod_le_prod' (fun i _ => Finset.card_le_card (h i))

theorem eq_of_refines_of_completionCount_eq {A B : OrderBox ι} (h : A.Refines B)
    (hp : 0 < completionCount B) (hc : completionCount A = completionCount B) : A = B := by
  have hs : completions A = completions B :=
    Finset.eq_of_subset_of_card_le h.completions_subset (by simpa only [completions_card] using hc.ge)
  have hA := (completionCount_pos_iff A).mp (hc ▸ hp)
  have hB := (completionCount_pos_iff B).mp hp
  funext i
  have ha := Fintype.eval_image_piFinset A i (fun j _ => hA j)
  have hb := Fintype.eval_image_piFinset B i (fun j _ => hB j)
  change (completions A).image (fun k => k i) = A i at ha
  change (completions B).image (fun k => k i) = B i at hb
  rw [← ha,hs,hb]

theorem completionCount_lt_of_refines_ne {A B : OrderBox ι} (h : A.Refines B)
    (hp : 0 < completionCount B) (hne : A ≠ B) : completionCount A < completionCount B := by
  exact lt_of_le_of_ne h.completionCount_le
    (fun he => hne (eq_of_refines_of_completionCount_eq h hp he))

def stabilize (update : OrderBox ι → OrderBox ι)
    (hupdate : ∀ B, (update B).Refines B) (B : OrderBox ι) : OrderBox ι :=
  if _h : completionCount (update B) = completionCount B then update B
  else stabilize update hupdate (update B)
termination_by completionCount B
decreasing_by
  exact lt_of_le_of_ne (hupdate B).completionCount_le _h

omit [DecidableEq ι] in
theorem stabilize_refines (update : OrderBox ι → OrderBox ι)
    (hupdate : ∀ B, (update B).Refines B) (B : OrderBox ι) :
    (stabilize update hupdate B).Refines B := by
  rw [stabilize]
  split_ifs with h
  · exact hupdate B
  · exact (stabilize_refines update hupdate (update B)).trans (hupdate B)
termination_by completionCount B
decreasing_by exact lt_of_le_of_ne (hupdate B).completionCount_le h

theorem stabilize_terminal (update : OrderBox ι → OrderBox ι)
    (hupdate : ∀ B, (update B).Refines B) (B : OrderBox ι) :
    completionCount (stabilize update hupdate B) = 0 ∨
      update (stabilize update hupdate B) = stabilize update hupdate B := by
  rw [stabilize]
  split_ifs with h
  · by_cases hp : completionCount B = 0
    · exact Or.inl (h.trans hp)
    · have he := eq_of_refines_of_completionCount_eq (hupdate B) (Nat.pos_of_ne_zero hp) h
      exact Or.inr (by rw [he]; exact he)
  · exact stabilize_terminal update hupdate (update B)
termination_by completionCount B
decreasing_by exact lt_of_le_of_ne (hupdate B).completionCount_le h

omit [DecidableEq ι] in
theorem stabilize_preserves (update : OrderBox ι → OrderBox ι)
    (hupdate : ∀ B, (update B).Refines B) (P : OrderBox ι → Prop)
    (hP : ∀ B, P B → P (update B)) (B : OrderBox ι) (hB : P B) :
    P (stabilize update hupdate B) := by
  rw [stabilize]
  split_ifs with h
  · exact hP B hB
  · exact stabilize_preserves update hupdate P hP (update B) (hP B hB)
termination_by completionCount B
decreasing_by exact lt_of_le_of_ne (hupdate B).completionCount_le h

theorem stabilize_fixed_of_admits (update : OrderBox ι → OrderBox ι)
    (hupdate : ∀ B, (update B).Refines B) (B : OrderBox ι) (k : ι → Fin 6)
    (hB : (stabilize update hupdate B).Admits k) :
    update (stabilize update hupdate B) = stabilize update hupdate B := by
  rcases stabilize_terminal update hupdate B with hz | hf
  · exact (Nat.ne_of_gt hB.completionCount_pos hz).elim
  · exact hf

end OrderBox
end CentralConfigurations
