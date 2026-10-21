import CentralConfigurations.Enumeration.Section7OrderFamilies

/-! Simultaneous vertex relabeling of symmetric z/w order arrays.
Both colors use the same permutation. Diagonal/off-diagonal status and
the number of singleton completions are unchanged. -/

namespace CentralConfigurations

namespace UpperIndex

def relabel {n : ℕ} (e : Equiv.Perm (Fin n)) (p : UpperIndex n) : UpperIndex n :=
  upperIndex (e p.1.1) (e p.1.2)

theorem relabel_upperIndex {n : ℕ} (e : Equiv.Perm (Fin n)) (i j : Fin n) :
    relabel e (upperIndex i j) = upperIndex (e i) (e j) := by
  rcases le_total i j with hij | hji
  · simp only [relabel,upperIndex,min_eq_left hij,max_eq_right hij]
  · change upperIndex (e (min i j)) (e (max i j)) = _
    rw [min_eq_right hji,max_eq_left hji,upperIndex_symm]

theorem relabel_refl {n : ℕ} (p : UpperIndex n) : relabel (Equiv.refl _) p = p :=
  upperIndex_of_le p

theorem relabel_relabel {n : ℕ} (e f : Equiv.Perm (Fin n)) (p : UpperIndex n) :
    relabel e (relabel f p) = relabel (f.trans e) p :=
  relabel_upperIndex e (f p.1.1) (f p.1.2)

theorem relabel_inverse {n : ℕ} (e : Equiv.Perm (Fin n)) (p : UpperIndex n) :
    relabel e.symm (relabel e p) = p := by
  change relabel e.symm (upperIndex (e p.1.1) (e p.1.2)) = p
  rw [relabel_upperIndex]
  simpa only [Equiv.symm_apply_apply] using upperIndex_of_le p

theorem relabel_diagonal_iff {n : ℕ} (e : Equiv.Perm (Fin n)) (p : UpperIndex n) :
    (relabel e p).1.1 = (relabel e p).1.2 ↔ p.1.1 = p.1.2 := by
  rcases le_total (e p.1.1) (e p.1.2) with hij | hji
  · simp [relabel,upperIndex,min_eq_left hij,max_eq_right hij,e.injective.eq_iff]
  · simp [relabel,upperIndex,min_eq_right hji,max_eq_left hji,e.injective.eq_iff,eq_comm]

end UpperIndex

namespace ZWOrderIndex

def relabel {n : ℕ} (e : Equiv.Perm (Fin n)) (p : ZWOrderIndex n) : ZWOrderIndex n :=
  (p.1,UpperIndex.relabel e p.2)

theorem relabel_refl {n : ℕ} (p : ZWOrderIndex n) : relabel (Equiv.refl _) p = p := by
  simp only [relabel,UpperIndex.relabel_refl]

theorem relabel_relabel {n : ℕ} (e f : Equiv.Perm (Fin n)) (p : ZWOrderIndex n) :
    relabel e (relabel f p) = relabel (f.trans e) p := by
  simp only [relabel,UpperIndex.relabel_relabel]

theorem relabel_inverse {n : ℕ} (e : Equiv.Perm (Fin n)) (p : ZWOrderIndex n) :
    relabel e.symm (relabel e p) = p := by
  simp only [relabel,UpperIndex.relabel_inverse]

def perm {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (ZWOrderIndex n) where
  toFun := relabel e
  invFun := relabel e.symm
  left_inv := relabel_inverse e
  right_inv := by intro p; simpa only [Equiv.symm_symm] using relabel_inverse e.symm p

theorem relabel_diagonal_iff {n : ℕ} (e : Equiv.Perm (Fin n)) (p : ZWOrderIndex n) :
    (relabel e p).2.1.1 = (relabel e p).2.1.2 ↔ p.2.1.1 = p.2.1.2 :=
  UpperIndex.relabel_diagonal_iff e p.2

theorem relabel_slot {n : ℕ} (e : Equiv.Perm (Fin n)) (c : Fin 2) (i j : Fin n) :
    relabel e (zwOrderSlot c i j) = zwOrderSlot c (e i) (e j) := by
  simp only [relabel,zwOrderSlot,UpperIndex.relabel_upperIndex]

end ZWOrderIndex

def relabelZWOrder {n : ℕ} {α : Type*} (B : ZWOrderIndex n → α)
    (e : Equiv.Perm (Fin n)) : ZWOrderIndex n → α := fun p => B (ZWOrderIndex.relabel e p)

theorem relabelZWOrder_refl {n : ℕ} {α : Type*} (B : ZWOrderIndex n → α) :
    relabelZWOrder B (Equiv.refl _) = B := by
  funext p
  simp only [relabelZWOrder,ZWOrderIndex.relabel_refl]

theorem relabelZWOrder_relabel {n : ℕ} {α : Type*} (B : ZWOrderIndex n → α)
    (e f : Equiv.Perm (Fin n)) :
    relabelZWOrder (relabelZWOrder B e) f = relabelZWOrder B (f.trans e) := by
  funext p
  simp only [relabelZWOrder,ZWOrderIndex.relabel_relabel]

theorem relabelZWOrder_inverse {n : ℕ} {α : Type*} (B : ZWOrderIndex n → α)
    (e : Equiv.Perm (Fin n)) : relabelZWOrder (relabelZWOrder B e) e.symm = B := by
  funext p
  simpa only [relabelZWOrder,Equiv.symm_symm] using
    congrArg B (ZWOrderIndex.relabel_inverse e.symm p)

theorem relabelZWOrder_injective {n : ℕ} {α : Type*} (e : Equiv.Perm (Fin n)) :
    Function.Injective (fun B : ZWOrderIndex n → α => relabelZWOrder B e) := by
  intro A B h
  have := congrArg (fun C => relabelZWOrder C e.symm) h
  simpa only [relabelZWOrder_inverse] using this

theorem relabelZWOrder_admits_iff {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (k : ZWOrderIndex n → Fin 6) (e : Equiv.Perm (Fin n)) :
    OrderBox.Admits (relabelZWOrder B e) (relabelZWOrder k e) ↔ B.Admits k := by
  constructor
  · intro h p
    obtain ⟨r,hr⟩ := (ZWOrderIndex.perm e).surjective p
    exact hr ▸ h r
  · intro h p
    exact h (ZWOrderIndex.relabel e p)

theorem relabelZWOrder_refines_iff {n : ℕ} (A B : OrderBox (ZWOrderIndex n))
    (e : Equiv.Perm (Fin n)) :
    OrderBox.Refines (relabelZWOrder A e) (relabelZWOrder B e) ↔ A.Refines B := by
  constructor
  · intro h p
    obtain ⟨r,hr⟩ := (ZWOrderIndex.perm e).surjective p
    exact hr ▸ h r
  · intro h p
    exact h (ZWOrderIndex.relabel e p)

theorem relabelZWOrder_completionCount {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (e : Equiv.Perm (Fin n)) :
    OrderBox.completionCount (relabelZWOrder B e) = OrderBox.completionCount B :=
  Equiv.prod_comp (ZWOrderIndex.perm e) (fun p => (B p).card)

theorem IsType2OrderBox.relabel {n : ℕ} {B : OrderBox (ZWOrderIndex n)}
    (hB : IsType2OrderBox B) (e : Equiv.Perm (Fin n)) : IsType2OrderBox (relabelZWOrder B e) := by
  refine ⟨fun p => hB.1 _,fun p hp => hB.2 _ ?_⟩
  exact fun h => hp ((ZWOrderIndex.relabel_diagonal_iff e p).mp h)

theorem IsType3OrderBox.relabel {n : ℕ} {B : OrderBox (ZWOrderIndex n)}
    (hB : IsType3OrderBox B) (e : Equiv.Perm (Fin n)) : IsType3OrderBox (relabelZWOrder B e) :=
  fun p => hB (ZWOrderIndex.relabel e p)

end CentralConfigurations
