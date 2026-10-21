import CentralConfigurations.Enumeration.SequenceOrderDomains
import CentralConfigurations.Diagrams.SourceMaximalEdges

/-!
# Proposition 4.8: unique single edges in circled source components

The source component uses the matrix-power definition, with the printed
trace and ordered-pair uniqueness hypotheses. The theorem determines both
the own-color and companion levels. AppendixMaximalEdgeOrderDomains.lean
establishes the corresponding result for the appendix's component extraction.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

def UniqueSingleEdge {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℕ)
    (s : Finset (Fin n)) (i j : Fin n) : Prop :=
  i ∈ s ∧ j ∈ s ∧ i < j ∧ A i j = 1 ∧ B i j = 0 ∧
    ∀ u ∈ s, ∀ v ∈ s, u < v → A u v = 1 → B u v = 0 → u = i ∧ v = j

theorem UniqueSingleEdge.unordered {n : ℕ} {A B : Matrix (Fin n) (Fin n) ℕ}
    {s : Finset (Fin n)} {i j : Fin n} (h : UniqueSingleEdge A B s i j)
    (hA : ∀ u v, A u v = A v u) (hB : ∀ u v, B u v = B v u)
    (u : Fin n) (hu : u ∈ s) (v : Fin n) (hv : v ∈ s)
    (huv : u ≠ v) (ha : A u v = 1) (hb : B u v = 0) :
    (u = i ∧ v = j) ∨ (u = j ∧ v = i) := by
  rcases lt_or_gt_of_ne huv with huv | hvu
  · exact Or.inl (h.2.2.2.2.2 u hu v hv huv ha hb)
  · have he := h.2.2.2.2.2 v hv u hu hvu ((hA v u).trans ha) ((hB v u).trans hb)
    exact Or.inr ⟨he.2, he.1⟩

theorem OneColorLimit.exists_circle_of_trace_ne_zero {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (s : Finset (Fin n))
    (ht : (∑ i ∈ s, q.matrix i i) ≠ 0) : ∃ i ∈ s, q.position i ≠ 0 := by
  obtain ⟨i, hi, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht
  refine ⟨i, hi, ?_⟩
  simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hp

namespace OrderBox

variable {ι : Type*} [DecidableEq ι]

def setMaximalPair (B : OrderBox ι) (own companion : ι) : OrderBox ι :=
  Function.update (Function.update B own {5}) companion {1}

theorem Admits.setMaximalPair {B : OrderBox ι} {k : ι → Fin 6}
    (h : B.Admits k) (own companion : ι) (ho : k own = 5) (hc : k companion = 1) :
    (setMaximalPair B own companion).Admits k := by
  have h₁ := h.update_of_mem own {5} (by simpa using ho)
  exact h₁.update_of_mem companion {1} (by simpa using hc)

end OrderBox

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))

theorem unique_source_z_edge_five (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : SourceConnectedComponent l.z.matrix s)
    (ht : (∑ k ∈ s, l.z.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.z.matrix l.w.matrix s i j) : o.z i j = 5 := by
  apply (o.z_offDiagonal_five_iff l i j hu.2.2.1.ne).mpr
  exact l.unique_source_z_edge_maximal ha hm s hs
    (l.z.exists_circle_of_trace_ne_zero s ht) i j
    (hu.unordered l.z.matrix_symm l.w.matrix_symm)

theorem unique_source_w_edge_five (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : SourceConnectedComponent l.w.matrix s)
    (ht : (∑ k ∈ s, l.w.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.w.matrix l.z.matrix s i j) : o.w i j = 5 := by
  apply (o.w_offDiagonal_five_iff l i j hu.2.2.1.ne).mpr
  exact l.swap.unique_source_z_edge_maximal ha hm s hs
    (l.w.exists_circle_of_trace_ne_zero s ht) i j
    (hu.unordered l.w.matrix_symm l.z.matrix_symm)

variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem unique_source_z_edge_levels (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : SourceConnectedComponent l.z.matrix s)
    (ht : (∑ k ∈ s, l.z.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.z.matrix l.w.matrix s i j) :
    o.z i j = 5 ∧ o.w i j = 1 := by
  have hz := o.unique_source_z_edge_five l hm s hs ht i j hu
  have hij := hu.2.2.1.ne
  have hf : l.z.force i j ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij] using hu.2.2.2.1
  have he := o.edge_level_sum l hb i j hij (Or.inl hf)
  refine ⟨hz, ?_⟩
  apply Fin.ext
  simp only [hz] at he
  omega

theorem unique_source_w_edge_levels (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : SourceConnectedComponent l.w.matrix s)
    (ht : (∑ k ∈ s, l.w.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.w.matrix l.z.matrix s i j) :
    o.w i j = 5 ∧ o.z i j = 1 := by
  have hw := o.unique_source_w_edge_five l hm s hs ht i j hu
  have hij := hu.2.2.1.ne
  have hf : l.w.force i j ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij] using hu.2.2.2.1
  have he := o.edge_level_sum l hb i j hij (Or.inr hf)
  refine ⟨hw, ?_⟩
  apply Fin.ext
  simp only [hw] at he
  omega

theorem admitted_sourceMaximalZPair (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : SourceConnectedComponent l.z.matrix s)
    (ht : (∑ k ∈ s, l.z.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.z.matrix l.w.matrix s i j)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    (OrderBox.setMaximalPair B (zwOrderSlot 0 i j) (zwOrderSlot 1 i j)).Admits o.orderCode := by
  have h := o.unique_source_z_edge_levels l hb hm s hs ht i j hu
  exact hB.setMaximalPair _ _ (by simpa only [orderCode_z] using h.1)
    (by simpa only [orderCode_w] using h.2)

theorem admitted_sourceMaximalWPair (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : SourceConnectedComponent l.w.matrix s)
    (ht : (∑ k ∈ s, l.w.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.w.matrix l.z.matrix s i j)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    (OrderBox.setMaximalPair B (zwOrderSlot 1 i j) (zwOrderSlot 0 i j)).Admits o.orderCode := by
  have h := o.unique_source_w_edge_levels l hb hm s hs ht i j hu
  exact hB.setMaximalPair _ _ (by simpa only [orderCode_w] using h.1)
    (by simpa only [orderCode_z] using h.2)

end SequenceOrderAssignment

namespace ZWOrderCoverage

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable {C : Finset (OrderBox (ZWOrderIndex n))}

theorem sourceMaximalZPair (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : SourceConnectedComponent l.z.matrix s)
    (ht : (∑ k ∈ s, l.z.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.z.matrix l.w.matrix s i j) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha
      (C.image fun B => OrderBox.setMaximalPair B (zwOrderSlot 0 i j) (zwOrderSlot 1 i j)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_sourceMaximalZPair (l.comp φ hφ.tendsto_atTop) (fun t => hb (φ t))
      hm s hs ht i j hu B ho⟩

theorem sourceMaximalWPair (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : SourceConnectedComponent l.w.matrix s)
    (ht : (∑ k ∈ s, l.w.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.w.matrix l.z.matrix s i j) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha
      (C.image fun B => OrderBox.setMaximalPair B (zwOrderSlot 1 i j) (zwOrderSlot 0 i j)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_sourceMaximalWPair (l.comp φ hφ.tendsto_atTop) (fun t => hb (φ t))
      hm s hs ht i j hu B ho⟩

end ZWOrderCoverage

end CentralConfigurations
