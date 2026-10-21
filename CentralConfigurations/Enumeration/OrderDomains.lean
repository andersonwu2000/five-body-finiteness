import CentralConfigurations.Diagrams.OrderTriangleRules
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Powerset

/-!
# Finite order domains and sound refinement

A box assigns a finite set of levels to each matrix entry. Coverage of a
family is existential: each actual level assignment must belong to some
box. Combining two covering families therefore takes pairwise pointwise
intersections, not the ordinary intersection of the families as sets.

The triangle filter is the exact min/max filter of Proposition 4.5.
Empty auxiliary domains have total min/max values; an admitted assignment
ensures that every domain used in the soundness proof is nonempty.
-/

namespace CentralConfigurations

abbrev OrderBox (ι : Type*) := ι → Finset (Fin 6)

namespace OrderBox

variable {ι : Type*}

def Admits (B : OrderBox ι) (k : ι → Fin 6) : Prop := ∀ i, k i ∈ B i

def Refines (B A : OrderBox ι) : Prop := ∀ i, B i ⊆ A i

def intersect (A B : OrderBox ι) : OrderBox ι := fun i => A i ∩ B i

theorem admits_intersect_iff {A B : OrderBox ι} {k : ι → Fin 6} :
    (intersect A B).Admits k ↔ A.Admits k ∧ B.Admits k := by
  constructor
  · intro h
    exact ⟨fun i => (Finset.mem_inter.mp (h i)).1,
      fun i => (Finset.mem_inter.mp (h i)).2⟩
  · rintro ⟨ha, hb⟩ i
    exact Finset.mem_inter.mpr ⟨ha i, hb i⟩

theorem intersect_refines_left (A B : OrderBox ι) : (intersect A B).Refines A :=
  fun _ => Finset.inter_subset_left

theorem Admits.mono {A B : OrderBox ι} {k : ι → Fin 6}
    (h : B.Admits k) (hBA : B.Refines A) : A.Admits k := fun i => hBA i (h i)

def triangleFilter (A B C : Finset (Fin 6)) : Finset (Fin 6) :=
  A.filter fun a => a ≤ max (B.sup id) (C.sup id) ∧
    B.inf id ≤ max a (C.sup id) ∧ C.inf id ≤ max a (B.sup id)

theorem triangleFilter_subset (A B C : Finset (Fin 6)) : triangleFilter A B C ⊆ A :=
  Finset.filter_subset _ _

theorem mem_triangleFilter {A B C : Finset (Fin 6)} {a b c : Fin 6}
    (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C) (ht : OrderTriangle a b c) :
    a ∈ triangleFilter A B C := by
  apply Finset.mem_filter.mpr
  refine ⟨ha, ?_, ?_, ?_⟩
  · exact ht.1.trans (max_le_max (Finset.le_sup (f := id) hb) (Finset.le_sup (f := id) hc))
  · exact (Finset.inf_le (f := id) hb).trans
      (ht.2.1.trans (max_le_max_left _ (Finset.le_sup (f := id) hc)))
  · exact (Finset.inf_le (f := id) hc).trans
      (ht.2.2.trans (max_le_max_left _ (Finset.le_sup (f := id) hb)))

variable [DecidableEq ι]

theorem Admits.update_of_mem {B : OrderBox ι} {k : ι → Fin 6}
    (h : B.Admits k) (i : ι) (S : Finset (Fin 6)) (hi : k i ∈ S) :
    Admits (Function.update B i S) k := by
  intro j
  by_cases hji : j = i
  · subst j; simpa only [Function.update_self] using hi
  · simpa only [Function.update_of_ne hji] using h j

def equalizeTriple (B : OrderBox ι) (x y z : ι) : OrderBox ι :=
  let S := B x ∩ B y ∩ B z
  Function.update (Function.update (Function.update B x S) y S) z S

theorem Admits.equalizeTriple {B : OrderBox ι} {k : ι → Fin 6}
    (h : B.Admits k) (x y z : ι) (hxy : k x = k y) (hxz : k x = k z) :
    (equalizeTriple B x y z).Admits k := by
  let S := B x ∩ B y ∩ B z
  have hx : k x ∈ S := Finset.mem_inter.mpr
    ⟨Finset.mem_inter.mpr ⟨h x, hxy.symm ▸ h y⟩, hxz.symm ▸ h z⟩
  have h₁ := h.update_of_mem x S hx
  have h₂ := h₁.update_of_mem y S (hxy ▸ hx)
  exact h₂.update_of_mem z S (hxz ▸ hx)

def triangleRefineAt (B : OrderBox ι) (x y z : ι) : OrderBox ι :=
  Function.update B x (triangleFilter (B x) (B y) (B z))

theorem triangleRefineAt_refines (B : OrderBox ι) (x y z : ι) :
    (triangleRefineAt B x y z).Refines B := by
  intro i
  by_cases hi : i = x
  · subst i
    simpa only [triangleRefineAt, Function.update_self] using triangleFilter_subset (B x) (B y) (B z)
  · simp only [triangleRefineAt, Function.update_of_ne hi]
    exact Finset.Subset.refl _

theorem Admits.triangleRefineAt {B : OrderBox ι} {k : ι → Fin 6}
    (h : B.Admits k) (x y z : ι) (ht : OrderTriangle (k x) (k y) (k z)) :
    (triangleRefineAt B x y z).Admits k := by
  intro i
  by_cases hi : i = x
  · subst i
    simpa only [OrderBox.triangleRefineAt, Function.update_self] using
      mem_triangleFilter (h x) (h y) (h z) ht
  · simpa only [OrderBox.triangleRefineAt, Function.update_of_ne hi] using h i

/-- The separation update followed by the two endpoint updates in Proposition
4.5. An upper-triangular matrix index also updates its symmetric entry. -/
def coordinateTriangleStep (B : OrderBox ι) (edge leg₁ leg₂ left right : ι) : OrderBox ι :=
  let B₁ := triangleRefineAt B edge leg₁ leg₂
  let B₂ := triangleRefineAt B₁ left edge right
  triangleRefineAt B₂ right edge left

theorem Admits.coordinateTriangleStep {B : OrderBox ι} {k : ι → Fin 6}
    (h : B.Admits k) (edge leg₁ leg₂ left right : ι)
    (he : OrderTriangle (k edge) (k leg₁) (k leg₂))
    (hp : OrderTriangle (k edge) (k left) (k right)) :
    (coordinateTriangleStep B edge leg₁ leg₂ left right).Admits k := by
  have h₁ := h.triangleRefineAt edge leg₁ leg₂ he
  have h₂ := h₁.triangleRefineAt left edge right hp.swap_left
  exact h₂.triangleRefineAt right edge left hp.rotate

section Families

variable [Fintype ι]

def CoveredBy (C : Finset (OrderBox ι)) (k : ι → Fin 6) : Prop :=
  ∃ B ∈ C, B.Admits k

def branchAt (B : OrderBox ι) (i : ι) : Finset (OrderBox ι) :=
  (B i).image fun a => Function.update B i {a}

theorem covered_branchAt_iff (B : OrderBox ι) (i : ι) (k : ι → Fin 6) :
    CoveredBy (branchAt B i) k ↔ B.Admits k := by
  constructor
  · rintro ⟨C, hC, hk⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hC
    intro j
    by_cases hji : j = i
    · subst j
      have he : k i = a := by simpa only [Function.update_self, Finset.mem_singleton] using hk i
      exact he.symm ▸ ha
    · simpa only [Function.update_of_ne hji] using hk j
  · intro hk
    refine ⟨Function.update B i {k i}, Finset.mem_image.mpr ⟨k i, hk i, rfl⟩, ?_⟩
    intro j
    by_cases hji : j = i
    · subst j; simp
    · simpa only [Function.update_of_ne hji] using hk j

def pairwiseIntersections (C D : Finset (OrderBox ι)) : Finset (OrderBox ι) :=
  C.biUnion fun A => D.image fun B => intersect A B

omit [DecidableEq ι] in
theorem covered_pairwiseIntersections_iff (C D : Finset (OrderBox ι)) (k : ι → Fin 6) :
    CoveredBy (pairwiseIntersections C D) k ↔ CoveredBy C k ∧ CoveredBy D k := by
  constructor
  · rintro ⟨E, hE, hk⟩
    obtain ⟨A, hA, hAE⟩ := Finset.mem_biUnion.mp hE
    obtain ⟨B, hB, hBE⟩ := Finset.mem_image.mp hAE
    rw [← hBE] at hk
    have h := admits_intersect_iff.mp hk
    exact ⟨⟨A, hA, h.1⟩, ⟨B, hB, h.2⟩⟩
  · rintro ⟨⟨A, hA, hkA⟩, ⟨B, hB, hkB⟩⟩
    exact ⟨intersect A B, Finset.mem_biUnion.mpr
      ⟨A, hA, Finset.mem_image.mpr ⟨B, hB, rfl⟩⟩,
      admits_intersect_iff.mpr ⟨hkA, hkB⟩⟩

def pruneEmpty (C : Finset (OrderBox ι)) : Finset (OrderBox ι) :=
  C.filter fun B => ∀ i, (B i).Nonempty

omit [DecidableEq ι] in
theorem covered_pruneEmpty_iff (C : Finset (OrderBox ι)) (k : ι → Fin 6) :
    CoveredBy (pruneEmpty C) k ↔ CoveredBy C k := by
  constructor
  · rintro ⟨B, hB, hk⟩
    exact ⟨B, (Finset.mem_filter.mp hB).1, hk⟩
  · rintro ⟨B, hB, hk⟩
    exact ⟨B, Finset.mem_filter.mpr ⟨hB, fun i => ⟨k i, hk i⟩⟩, hk⟩

def branchFamilyAt (C : Finset (OrderBox ι)) (i : ι) : Finset (OrderBox ι) :=
  C.biUnion fun B => branchAt B i

theorem covered_branchFamilyAt_iff (C : Finset (OrderBox ι)) (i : ι) (k : ι → Fin 6) :
    CoveredBy (branchFamilyAt C i) k ↔ CoveredBy C k := by
  constructor
  · rintro ⟨E, hE, hk⟩
    obtain ⟨B, hB, hBE⟩ := Finset.mem_biUnion.mp hE
    exact ⟨B, hB, (covered_branchAt_iff B i k).mp ⟨E, hBE, hk⟩⟩
  · rintro ⟨B, hB, hk⟩
    obtain ⟨E, hE, hkE⟩ := (covered_branchAt_iff B i k).mpr hk
    exact ⟨E, Finset.mem_biUnion.mpr ⟨B, hB, hE⟩, hkE⟩

end Families

end OrderBox

end CentralConfigurations
