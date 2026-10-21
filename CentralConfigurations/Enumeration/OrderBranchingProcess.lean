import CentralConfigurations.Enumeration.OrderDomainTermination

/-! Section 7: refine, prune, and split one coordinate at a time.
The recursion is on a finite list of slots; refinements cannot reopen a
resolved coordinate. Thus the list is sufficient even when later filters
change other entries. Every leaf refines an original input box. -/

namespace CentralConfigurations
namespace OrderBox
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def refinePrune (update : OrderBox ι → OrderBox ι)
    (C : Finset (OrderBox ι)) : Finset (OrderBox ι) := pruneEmpty (C.image update)

def splitRefine (update : OrderBox ι → OrderBox ι) :
    List ι → Finset (OrderBox ι) → Finset (OrderBox ι)
  | [], C => refinePrune update C
  | i :: slots, C => splitRefine update slots (branchFamilyAt (refinePrune update C) i)

omit [DecidableEq ι] in
theorem mem_refinePrune_iff (update : OrderBox ι → OrderBox ι)
    (C : Finset (OrderBox ι)) (D : OrderBox ι) :
    D ∈ refinePrune update C ↔ (∀ i, (D i).Nonempty) ∧ ∃ B ∈ C, update B = D := by
  simp only [refinePrune,pruneEmpty,Finset.mem_filter,Finset.mem_image]
  tauto

theorem mem_branchAt_properties (B D : OrderBox ι) (i : ι) (hD : D ∈ branchAt B i) :
    D.Refines B ∧ (D i).card = 1 := by
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hD
  constructor
  · intro j b hb
    by_cases hji : j = i
    · subst j
      have he : b = a := by simpa only [Function.update_self,Finset.mem_singleton] using hb
      exact he ▸ ha
    · simpa only [Function.update_of_ne hji] using hb
  · simp

omit [Fintype ι] [DecidableEq ι] in
theorem singleton_card_of_refines {B D : OrderBox ι} (h : D.Refines B)
    (i : ι) (hi : (D i).Nonempty) (hb : (B i).card = 1) : (D i).card = 1 := by
  have hle := Finset.card_le_card (h i)
  have hpos := Finset.card_pos.mpr hi
  omega

theorem mem_splitRefine_properties (update : OrderBox ι → OrderBox ι)
    (hupdate : ∀ B, (update B).Refines B) (slots : List ι)
    (C : Finset (OrderBox ι)) (D : OrderBox ι) (hD : D ∈ splitRefine update slots C) :
    (∀ i, (D i).Nonempty) ∧ (∃ B ∈ C, D.Refines B) ∧
      ∀ i ∈ slots, (D i).card = 1 := by
  induction slots generalizing C with
  | nil =>
    obtain ⟨hN,B,hB,rfl⟩ := (mem_refinePrune_iff update C D).mp hD
    exact ⟨hN,⟨B,hB,hupdate B⟩,by simp⟩
  | cons i slots ih =>
    obtain ⟨hN,⟨E,hE,hDE⟩,hslots⟩ := ih _ hD
    obtain ⟨A,hA,hEA⟩ := Finset.mem_biUnion.mp hE
    obtain ⟨_,B,hB,hAB⟩ := (mem_refinePrune_iff update C A).mp hA
    obtain ⟨hEA',hEi⟩ := mem_branchAt_properties A E i hEA
    have hDB : D.Refines B := hDE.trans (hEA'.trans (hAB ▸ hupdate B))
    refine ⟨hN,⟨B,hB,hDB⟩,?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with rfl | hj
    · exact singleton_card_of_refines hDE j (hN j) hEi
    · exact hslots j hj

theorem covered_refinePrune (update : OrderBox ι → OrderBox ι)
    (C : Finset (OrderBox ι)) (k : ι → Fin 6)
    (hupdate : ∀ B, B.Admits k → (update B).Admits k) (hC : CoveredBy C k) :
    CoveredBy (refinePrune update C) k := by
  obtain ⟨B,hB,hk⟩ := hC
  have h := hupdate B hk
  exact ⟨update B,(mem_refinePrune_iff update C _).mpr
    ⟨fun i => ⟨k i,h i⟩,B,hB,rfl⟩,h⟩

theorem covered_splitRefine (update : OrderBox ι → OrderBox ι)
    (slots : List ι) (C : Finset (OrderBox ι)) (k : ι → Fin 6)
    (hupdate : ∀ B, B.Admits k → (update B).Admits k) (hC : CoveredBy C k) :
    CoveredBy (splitRefine update slots C) k := by
  induction slots generalizing C with
  | nil => exact covered_refinePrune update C k hupdate hC
  | cons i slots ih =>
    exact ih _ ((covered_branchFamilyAt_iff _ i k).mpr
      (covered_refinePrune update C k hupdate hC))

theorem mem_splitRefine_last (update : OrderBox ι → OrderBox ι)
    (slots : List ι) (C : Finset (OrderBox ι)) (D : OrderBox ι)
    (hD : D ∈ splitRefine update slots C) : ∃ B, update B = D := by
  induction slots generalizing C with
  | nil =>
    obtain ⟨_,B,_,hB⟩ := (mem_refinePrune_iff update C D).mp hD
    exact ⟨B,hB⟩
  | cons i slots ih => exact ih _ hD

theorem completionCount_one_iff (B : OrderBox ι) :
    completionCount B = 1 ↔ ∀ i, (B i).card = 1 := by
  constructor
  · intro h
    have hN := (completionCount_pos_iff B).mp (by omega)
    obtain ⟨k,hk⟩ := Finset.card_eq_one.mp ((completions_card B).trans h)
    intro i
    have hi := Fintype.eval_image_piFinset B i (fun j _ => hN j)
    change (completions B).image (fun f => f i) = B i at hi
    rw [hk,Finset.image_singleton] at hi
    rw [← hi,Finset.card_singleton]
  · intro h
    simp [completionCount,h]

end OrderBox
end CentralConfigurations
