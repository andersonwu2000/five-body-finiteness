import CentralConfigurations.Enumeration.MaximalEdgeOrderDomains
import CentralConfigurations.Diagrams.AppendixMaximalEdges

/-!
# Proposition 4.8 for the actual Appendix II component extraction

The greedy fixed-power extraction preserves maximal-stroke endpoints in every
group containing a circle. Consequently its unique single edge has own level
5 and companion level 1. The resulting updates preserve all-subsequence
coverage for both colors, without a separate component-isolation assumption.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

theorem ScaledZWLimit.unique_appendix_z_edge_maximal {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : s ∈ appendixComponents l.z.matrix)
    (hc : ∃ r ∈ s, l.z.position r ≠ 0) (i j : Fin n)
    (hu : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → l.z.matrix u v = 1 → l.w.matrix u v = 0 →
      (u = i ∧ v = j) ∨ (u = j ∧ v = i)) : l.z.position i ≠ l.z.position j := by
  have hc' : ∃ r ∈ s, l.z.matrix r r = 1 := by
    obtain ⟨r, hr, hp⟩ := hc
    exact ⟨r, hr, by simp [OneColorLimit.matrix, OneColorLimit.Incident, hp]⟩
  obtain ⟨u, hus, v, hvs, hf, hp⟩ := l.z.appendix_component_exists_maximal_stroke hm s hs hc'
  have huv : u ≠ v := fun e => hp (congrArg l.z.position e)
  have hw : l.w.force u v = 0 := by
    by_contra hn
    exact hp (l.w_stroke_z_close ha u v huv hn)
  have hz : l.z.matrix u v = 1 := by
    simp [OneColorLimit.matrix, OneColorLimit.Incident, huv, hf]
  have hw' : l.w.matrix u v = 0 := by
    simp [OneColorLimit.matrix, OneColorLimit.Incident, huv, hw]
  rcases hu u hus v hvs huv hz hw' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hp
  · exact hp.symm

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))

theorem unique_appendix_z_edge_five (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : s ∈ appendixComponents l.z.matrix)
    (ht : (∑ k ∈ s, l.z.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.z.matrix l.w.matrix s i j) : o.z i j = 5 := by
  apply (o.z_offDiagonal_five_iff l i j hu.2.2.1.ne).mpr
  exact l.unique_appendix_z_edge_maximal ha hm s hs
    (l.z.exists_circle_of_trace_ne_zero s ht) i j
    (hu.unordered l.z.matrix_symm l.w.matrix_symm)

theorem unique_appendix_w_edge_five (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : s ∈ appendixComponents l.w.matrix)
    (ht : (∑ k ∈ s, l.w.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.w.matrix l.z.matrix s i j) : o.w i j = 5 := by
  apply (o.w_offDiagonal_five_iff l i j hu.2.2.1.ne).mpr
  exact l.swap.unique_appendix_z_edge_maximal ha hm s hs
    (l.w.exists_circle_of_trace_ne_zero s ht) i j
    (hu.unordered l.w.matrix_symm l.z.matrix_symm)

variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem unique_appendix_z_edge_levels (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : s ∈ appendixComponents l.z.matrix)
    (ht : (∑ k ∈ s, l.z.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.z.matrix l.w.matrix s i j) :
    o.z i j = 5 ∧ o.w i j = 1 := by
  have hz := o.unique_appendix_z_edge_five l hm s hs ht i j hu
  have hij := hu.2.2.1.ne
  have hf : l.z.force i j ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij] using hu.2.2.2.1
  have he := o.edge_level_sum l hb i j hij (Or.inl hf)
  refine ⟨hz, ?_⟩
  apply Fin.ext
  simp only [hz] at he
  omega

theorem unique_appendix_w_edge_levels (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : s ∈ appendixComponents l.w.matrix)
    (ht : (∑ k ∈ s, l.w.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.w.matrix l.z.matrix s i j) :
    o.w i j = 5 ∧ o.z i j = 1 := by
  have hw := o.unique_appendix_w_edge_five l hm s hs ht i j hu
  have hij := hu.2.2.1.ne
  have hf : l.w.force i j ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij] using hu.2.2.2.1
  have he := o.edge_level_sum l hb i j hij (Or.inr hf)
  refine ⟨hw, ?_⟩
  apply Fin.ext
  simp only [hw] at he
  omega

theorem admitted_appendixMaximalZPair (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : s ∈ appendixComponents l.z.matrix)
    (ht : (∑ k ∈ s, l.z.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.z.matrix l.w.matrix s i j)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    (OrderBox.setMaximalPair B (zwOrderSlot 0 i j) (zwOrderSlot 1 i j)).Admits o.orderCode := by
  have h := o.unique_appendix_z_edge_levels l hb hm s hs ht i j hu
  exact hB.setMaximalPair _ _ (by simpa only [orderCode_z] using h.1)
    (by simpa only [orderCode_w] using h.2)

theorem admitted_appendixMaximalWPair (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : s ∈ appendixComponents l.w.matrix)
    (ht : (∑ k ∈ s, l.w.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.w.matrix l.z.matrix s i j)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    (OrderBox.setMaximalPair B (zwOrderSlot 1 i j) (zwOrderSlot 0 i j)).Admits o.orderCode := by
  have h := o.unique_appendix_w_edge_levels l hb hm s hs ht i j hu
  exact hB.setMaximalPair _ _ (by simpa only [orderCode_w] using h.1)
    (by simpa only [orderCode_z] using h.2)

end SequenceOrderAssignment

namespace ZWOrderCoverage

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable {C : Finset (OrderBox (ZWOrderIndex n))}

theorem appendixMaximalZPair (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : s ∈ appendixComponents l.z.matrix)
    (ht : (∑ k ∈ s, l.z.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.z.matrix l.w.matrix s i j) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha
      (C.image fun B => OrderBox.setMaximalPair B (zwOrderSlot 0 i j) (zwOrderSlot 1 i j)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_appendixMaximalZPair (l.comp φ hφ.tendsto_atTop) (fun t => hb (φ t))
      hm s hs ht i j hu B ho⟩

theorem appendixMaximalWPair (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : s ∈ appendixComponents l.w.matrix)
    (ht : (∑ k ∈ s, l.w.matrix k k) ≠ 0) (i j : Fin n)
    (hu : UniqueSingleEdge l.w.matrix l.z.matrix s i j) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha
      (C.image fun B => OrderBox.setMaximalPair B (zwOrderSlot 1 i j) (zwOrderSlot 0 i j)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_appendixMaximalWPair (l.comp φ hφ.tendsto_atTop) (fun t => hb (φ t))
      hm s hs ht i j hu B ho⟩

end ZWOrderCoverage

end CentralConfigurations
