import CentralConfigurations.FiveBody.RZeroCard
import CentralConfigurations.Enumeration.FourProductTransport
import CentralConfigurations.FiveBody.FixedLevelFiniteness
import CentralConfigurations.FiveBody.InvariantPoleExtraction

/-! Exact transport of the whole labelled R-list and its selected product.
Each permutation acts on both masses and actual configurations. -/

namespace CentralConfigurations.FiveBody.RZero
noncomputable section
open scoped BigOperators

def edgeIndex : Fin 5 → Fin 5 → Fin 10 :=
  ![![0,0,1,2,3], ![0,0,4,5,6], ![1,4,0,7,8],
    ![2,5,7,0,9], ![3,6,8,9,0]]

def relabelIndex (σ : Equiv.Perm (Fin 5)) (e : Fin 10) : Fin 10 :=
  edgeIndex (σ (fiveBodyEdges e).1) (σ (fiveBodyEdges e).2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem relabelIndex_bijective : ∀ σ : Equiv.Perm (Fin 5),
    Function.Bijective (relabelIndex σ) := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem tripleLabels_relabelIndex : ∀ σ : Equiv.Perm (Fin 5), ∀ e : Fin 10,
    tripleLabels (relabelIndex σ e) = (tripleLabels e).image σ := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem fourProductEdgeList_relabelIndex : ∀ σ : Equiv.Perm (Fin 5), ∀ e : Fin 10,
    ((fiveBodyFourProductEdgeList e).map (fun p =>
      orderedFiveBodyPair (σ p.1, σ p.2))).Perm
      (fiveBodyFourProductEdgeList (relabelIndex σ e)) := by decide +kernel

theorem mem_completeR_relabel (mass : Fin 5 → ℝ) (hm : ∀ i, 0 < mass i)
    (σ : Equiv.Perm (Fin 5)) (e : Fin 10) :
    e ∈ completeR (mass ∘ σ) ↔ relabelIndex σ e ∈ completeR mass := by
  rw [mem_completeR_iff_additive (mass ∘ σ) (fun i => hm (σ i)) e,
    mem_completeR_iff_additive mass hm (relabelIndex σ e), tripleLabels_relabelIndex]
  exact additive_relabel_iff (reciprocalRoot mass) σ (tripleLabels e)

theorem completeR_card_relabel (mass : Fin 5 → ℝ) (hm : ∀ i, 0 < mass i)
    (σ : Equiv.Perm (Fin 5)) :
    (completeR (mass ∘ σ)).card = (completeR mass).card := by
  apply Finset.card_bij (fun e _ => relabelIndex σ e)
  · intro e he
    exact (mem_completeR_relabel mass hm σ e).mp he
  · intro a ha b hb hab
    exact (relabelIndex_bijective σ).injective hab
  · intro e he
    obtain ⟨k, hk⟩ := (relabelIndex_bijective σ).surjective e
    refine ⟨k, ?_, hk⟩
    exact (mem_completeR_relabel mass hm σ k).mpr (hk ▸ he)

theorem completeRProduct_relabel {K : Type*} [CommMonoid K]
    (mass : Fin 5 → ℝ) (hm : ∀ i, 0 < mass i)
    (σ : Equiv.Perm (Fin 5)) (Q : Fin 10 → K) :
    (∏ e ∈ completeR (mass ∘ σ), Q (relabelIndex σ e)) =
      ∏ e ∈ completeR mass, Q e := by
  apply Finset.prod_bij (fun e _ => relabelIndex σ e)
  · intro e he
    exact (mem_completeR_relabel mass hm σ e).mp he
  · intro a ha b hb hab
    exact (relabelIndex_bijective σ).injective hab
  · intro e he
    obtain ⟨k, hk⟩ := (relabelIndex_bijective σ).surjective e
    refine ⟨k, ?_, hk⟩
    exact (mem_completeR_relabel mass hm σ k).mpr (hk ▸ he)
  · intro e he
    rfl

theorem fourProduct_relabelIndex {K : Type*} [CommMonoid K]
    (d : Fin 5 → Fin 5 → K) (hd : ∀ a b, d a b = d b a)
    (σ : Equiv.Perm (Fin 5)) (e : Fin 10) :
    fiveBodyFourProducts (fun k => d (σ (fiveBodyEdges k).1) (σ (fiveBodyEdges k).2)) e =
      fiveBodyFourProducts (fun k => d (fiveBodyEdges k).1 (fiveBodyEdges k).2)
        (relabelIndex σ e) := by
  have h := ((fourProductEdgeList_relabelIndex σ e).map (fun p => d p.1 p.2)).prod_eq
  simpa only [List.map_map, Function.comp_def, symmetric_value_ordered_pair d hd,
    five_body_four_product_list] using h

theorem normalized_fourProduct_relabel (mass : Fin 5 → ℝ)
    (q : NormalizedSystem ℂ 5 (fun i => (mass i : ℂ)))
    (σ : Equiv.Perm (Fin 5)) (e : Fin 10) :
    (q.relabel σ).fiveBodyFourProduct e = q.fiveBodyFourProduct (relabelIndex σ e) := by
  have hd (a b : Fin 5) : squaredSeparation q.x q.y a b = squaredSeparation q.x q.y b a := by
    dsimp [squaredSeparation]
    ring
  exact fourProduct_relabelIndex (squaredSeparation q.x q.y) hd σ e

theorem normalized_selectedProduct_relabel (mass : Fin 5 → ℝ) (hm : ∀ i, 0 < mass i)
    (q : NormalizedSystem ℂ 5 (fun i => (mass i : ℂ)))
    (σ : Equiv.Perm (Fin 5)) :
    (q.relabel σ).fiveBodySelectedProduct (completeR (mass ∘ σ)) =
      q.fiveBodySelectedProduct (completeR mass) := by
  simp only [NormalizedSystem.fiveBodySelectedProduct, normalized_fourProduct_relabel]
  exact completeRProduct_relabel mass hm σ _

theorem zw_selectedProduct_relabel (mass : Fin 5 → ℝ) (hm : ∀ i, 0 < mass i)
    (q : ZWSystem ℂ 5 (fun i => (mass i : ℂ))) (σ : Equiv.Perm (Fin 5)) :
    (q.relabel σ).toNormalized.fiveBodySelectedProduct (completeR (mass ∘ σ)) =
      q.toNormalized.fiveBodySelectedProduct (completeR mass) :=
  normalized_selectedProduct_relabel mass hm q.toNormalized σ

theorem zw_selectedProduct_swap (mass : Fin 5 → ℝ)
    (q : ZWSystem ℂ 5 (fun i => (mass i : ℂ))) :
    q.swap.toNormalized.fiveBodySelectedProduct (completeR mass) =
      q.toNormalized.fiveBodySelectedProduct (completeR mass) := by
  simp only [NormalizedSystem.fiveBodySelectedProduct, ZWSystem.swap_fourProduct]

end
end CentralConfigurations.FiveBody.RZero
