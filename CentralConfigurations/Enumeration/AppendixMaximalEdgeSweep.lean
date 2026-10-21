import CentralConfigurations.Enumeration.AppendixMaximalEdgeOrderDomains
import Mathlib.Data.Finset.Prod

/-!
# Appendix II: the executable Proposition 4.8 initialization sweep

The source counts the two oriented occurrences of a single edge in each
component and requires a nonzero circle trace. Upper-triangular storage needs
only one of the two equivalent writes. Both greedy component lists are swept.
The update sets singleton domains, as the source does; arbitrary input boxes
need not be refined, but actual order assignments and coverage are preserved.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

def singleComponentEdges {n : ℕ} (A W : Matrix (Fin n) (Fin n) ℕ)
    (s : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (s ×ˢ s).filter fun p => p.1 ≠ p.2 ∧ A p.1 p.2 = 1 ∧ W p.1 p.2 = 0

theorem mem_singleComponentEdges {n : ℕ} (A W : Matrix (Fin n) (Fin n) ℕ)
    (s : Finset (Fin n)) (i j : Fin n) :
    (i, j) ∈ singleComponentEdges A W s ↔
      i ∈ s ∧ j ∈ s ∧ i ≠ j ∧ A i j = 1 ∧ W i j = 0 := by
  simp only [singleComponentEdges, Finset.mem_filter, Finset.mem_product]
  tauto

theorem uniqueSingleEdge_of_oriented_count_two {n : ℕ}
    {A W : Matrix (Fin n) (Fin n) ℕ} (hA : ∀ i j, A i j = A j i)
    (hW : ∀ i j, W i j = W j i) {s : Finset (Fin n)} {i j : Fin n}
    (hcount : (singleComponentEdges A W s).card = 2) (hij : i < j)
    (hm : (i, j) ∈ singleComponentEdges A W s) : UniqueSingleEdge A W s i j := by
  obtain ⟨hi, hj, hne, ha, hw⟩ := (mem_singleComponentEdges A W s i j).mp hm
  have hr : (j, i) ∈ singleComponentEdges A W s :=
    (mem_singleComponentEdges A W s j i).mpr
      ⟨hj, hi, hne.symm, (hA j i).trans ha, (hW j i).trans hw⟩
  have hp : (i, j) ≠ (j, i) := fun h => hne (congrArg Prod.fst h)
  have hsub : ({(i, j), (j, i)} : Finset (Fin n × Fin n)) ⊆ singleComponentEdges A W s := by
    intro p hp'
    rcases Finset.mem_insert.mp hp' with h | h
    · simpa only [h] using hm
    · have heq := Finset.mem_singleton.mp h
      simpa only [heq] using hr
  have he : ({(i, j), (j, i)} : Finset (Fin n × Fin n)) = singleComponentEdges A W s :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hcount, hp])
  refine ⟨hi, hj, hij, ha, hw, ?_⟩
  intro u hu v hv huv hau hwu
  have hm' : (u, v) ∈ ({(i, j), (j, i)} : Finset (Fin n × Fin n)) := by
    rw [he]
    exact (mem_singleComponentEdges A W s u v).mpr ⟨hu, hv, huv.ne, hau, hwu⟩
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hm'
  rcases hm' with h | ⟨rfl, rfl⟩
  · exact h
  · omega

theorem oriented_count_two_of_uniqueSingleEdge {n : ℕ}
    {A W : Matrix (Fin n) (Fin n) ℕ} (hA : ∀ i j, A i j = A j i)
    (hW : ∀ i j, W i j = W j i) {s : Finset (Fin n)} {i j : Fin n}
    (hu : UniqueSingleEdge A W s i j) : (singleComponentEdges A W s).card = 2 := by
  have he : singleComponentEdges A W s = {(i, j), (j, i)} := by
    ext ⟨u, v⟩
    rw [mem_singleComponentEdges]
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    constructor
    · rintro ⟨hu', hv', huv, hau, hwu⟩
      exact hu.unordered hA hW u hu' v hv' huv hau hwu
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨hu.1, hu.2.1, hu.2.2.1.ne, hu.2.2.2.1, hu.2.2.2.2.1⟩
      · exact ⟨hu.2.1, hu.1, hu.2.2.1.ne.symm, (hA _ _).trans hu.2.2.2.1,
          (hW _ _).trans hu.2.2.2.2.1⟩
  have hp : (i, j) ≠ (j, i) := fun h => hu.2.2.1.ne (congrArg Prod.fst h)
  simp [he, hp]

def appendixMaximalPairStep {n : ℕ} (A W : Matrix (Fin n) (Fin n) ℕ)
    (s : Finset (Fin n)) (own companion : Fin 2) (B : OrderBox (ZWOrderIndex n))
    (p : Fin n × Fin n) : OrderBox (ZWOrderIndex n) :=
  if (∑ i ∈ s, A i i) ≠ 0 ∧ (singleComponentEdges A W s).card = 2 ∧
      p.1 < p.2 ∧ p ∈ singleComponentEdges A W s then
    OrderBox.setMaximalPair B (zwOrderSlot own p.1 p.2) (zwOrderSlot companion p.1 p.2)
  else B

def appendixMaximalComponentSweep {n : ℕ} (A W : Matrix (Fin n) (Fin n) ℕ)
    (own companion : Fin 2) (B : OrderBox (ZWOrderIndex n)) (s : Finset (Fin n)) :
    OrderBox (ZWOrderIndex n) :=
  ((List.finRange n).flatMap fun i => (List.finRange n).map fun j => (i, j)).foldl
    (appendixMaximalPairStep A W s own companion) B

def appendixMaximalColorSweep {n : ℕ} (A W : Matrix (Fin n) (Fin n) ℕ)
    (own companion : Fin 2) (B : OrderBox (ZWOrderIndex n)) : OrderBox (ZWOrderIndex n) :=
  (appendixComponents A).foldl (appendixMaximalComponentSweep A W own companion) B

def appendixMaximalEdgesSweep {n : ℕ} (A W : Matrix (Fin n) (Fin n) ℕ)
    (B : OrderBox (ZWOrderIndex n)) : OrderBox (ZWOrderIndex n) :=
  appendixMaximalColorSweep W A 1 0 (appendixMaximalColorSweep A W 0 1 B)

theorem OrderBox.Admits.foldl {ι α : Type*} {k : ι → Fin 6} {B : OrderBox ι}
    (h : B.Admits k) (f : OrderBox ι → α → OrderBox ι) (xs : List α)
    (hf : ∀ a ∈ xs, ∀ D, D.Admits k → (f D a).Admits k) :
    (xs.foldl f B).Admits k := by
  induction xs generalizing B with
  | nil => exact h
  | cons a xs ih =>
      apply ih (hf a (by simp) B h)
      intro b hb D hD
      exact hf b (List.mem_cons_of_mem a hb) D hD

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass)
include hb hm

theorem admitted_appendixMaximalZStep (s : Finset (Fin n))
    (hs : s ∈ appendixComponents l.z.matrix) (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (p : Fin n × Fin n) :
    (appendixMaximalPairStep l.z.matrix l.w.matrix s 0 1 B p).Admits o.orderCode := by
  unfold appendixMaximalPairStep
  split_ifs with h
  · exact o.admitted_appendixMaximalZPair l hb hm s hs h.1 p.1 p.2
      (uniqueSingleEdge_of_oriented_count_two l.z.matrix_symm l.w.matrix_symm
        h.2.1 h.2.2.1 h.2.2.2) B hB
  · exact hB

theorem admitted_appendixMaximalWStep (s : Finset (Fin n))
    (hs : s ∈ appendixComponents l.w.matrix) (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (p : Fin n × Fin n) :
    (appendixMaximalPairStep l.w.matrix l.z.matrix s 1 0 B p).Admits o.orderCode := by
  unfold appendixMaximalPairStep
  split_ifs with h
  · exact o.admitted_appendixMaximalWPair l hb hm s hs h.1 p.1 p.2
      (uniqueSingleEdge_of_oriented_count_two l.w.matrix_symm l.z.matrix_symm
        h.2.1 h.2.2.1 h.2.2.2) B hB
  · exact hB

theorem admitted_appendixMaximalZComponent (s : Finset (Fin n))
    (hs : s ∈ appendixComponents l.z.matrix) (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) :
    (appendixMaximalComponentSweep l.z.matrix l.w.matrix 0 1 B s).Admits o.orderCode := by
  exact hB.foldl _ _ (fun p _ D hD => o.admitted_appendixMaximalZStep l hb hm s hs D hD p)

theorem admitted_appendixMaximalWComponent (s : Finset (Fin n))
    (hs : s ∈ appendixComponents l.w.matrix) (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) :
    (appendixMaximalComponentSweep l.w.matrix l.z.matrix 1 0 B s).Admits o.orderCode := by
  exact hB.foldl _ _ (fun p _ D hD => o.admitted_appendixMaximalWStep l hb hm s hs D hD p)

theorem admitted_appendixMaximalZColor (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) :
    (appendixMaximalColorSweep l.z.matrix l.w.matrix 0 1 B).Admits o.orderCode := by
  exact hB.foldl _ _ (fun s hs D hD => o.admitted_appendixMaximalZComponent l hb hm s hs D hD)

theorem admitted_appendixMaximalWColor (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) :
    (appendixMaximalColorSweep l.w.matrix l.z.matrix 1 0 B).Admits o.orderCode := by
  exact hB.foldl _ _ (fun s hs D hD => o.admitted_appendixMaximalWComponent l hb hm s hs D hD)

theorem admitted_appendixMaximalEdgesSweep (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) :
    (appendixMaximalEdgesSweep l.z.matrix l.w.matrix B).Admits o.orderCode :=
  o.admitted_appendixMaximalWColor l hb hm _ (o.admitted_appendixMaximalZColor l hb hm B hB)

end SequenceOrderAssignment

theorem ZWOrderCoverage.appendixMaximalEdgesSweep {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha
      (C.image (appendixMaximalEdgesSweep l.z.matrix l.w.matrix)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_appendixMaximalEdgesSweep (l.comp φ hφ.tendsto_atTop)
      (fun t => hb (φ t)) hm B ho⟩

end CentralConfigurations
