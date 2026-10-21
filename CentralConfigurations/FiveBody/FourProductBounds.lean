import CentralConfigurations.Enumeration.FourProductTransport
import CentralConfigurations.Asymptotics.CollapsedComplement
import CentralConfigurations.Enumeration.FiveBodySourceData

/-!
# The three complete-cluster diagrams have vanishing four-products

For four bodies in a double-edge clique, the internal squared distances are
O(epsilon^2) and the four external squared distances are O(epsilon^{-1}).
Each four-product consequently has upper order epsilon^2 or epsilon^5.
This applies to Chang's diagrams 2, 15 and 16, including all circle choices.
-/

namespace CentralConfigurations
noncomputable section
open scoped BigOperators Topology
open Filter Asymptotics

def fiveBodyEdgeTouches (v : Fin 5) (e : Fin 10) : Prop :=
  (fiveBodyEdges e).1 = v ∨ (fiveBodyEdges e).2 = v

instance (v : Fin 5) (e : Fin 10) : Decidable (fiveBodyEdgeTouches v e) :=
  inferInstanceAs (Decidable (_ = _ ∨ _ = _))

def fiveBodyClusterBound (eps : ℂ) (v : Fin 5) (e : Fin 10) : ℂ :=
  if fiveBodyEdgeTouches v e then eps⁻¹ else eps^2

theorem five_body_four_product_cluster_bound (eps : ℂ) (heps : eps ≠ 0)
    (v : Fin 5) (e : Fin 10) :
    fiveBodyFourProducts (fiveBodyClusterBound eps v) e =
      if fiveBodyEdgeTouches v e then eps^5 else eps^2 := by
  fin_cases v <;> fin_cases e <;>
    simp [fiveBodyFourProducts,fiveBodyClusterBound,fiveBodyEdgeTouches,
      fiveBodyEdges,fiveBodyDisjointEdges,Fin.prod_univ_succ] <;>
    field_simp [heps]

namespace OrderedDiagramRealization
variable {mass : Fin 5 → ℂ} {d : DiagramCode 5}
variable (r : OrderedDiagramRealization mass d)

theorem four_product_tendsto_zero_of_four_body_clique
    (hm : AdmissibleMasses mass) (v j : Fin 5) (hj : j ≠ v)
    (hc : ∀ a b, a ≠ v → b ≠ v → a ≠ b →
      r.leading.z.force a b ≠ 0 ∧ r.leading.w.force a b ≠ 0) (e : Fin 10) :
    Tendsto (fun t => (r.sequence t).fiveBodyFourProduct e) atTop (𝓝 0) := by
  let q := r.sequence
  let eps := fun t => ((q t).epsilon : ℂ)
  have heps (t) : eps t ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt ((q t).epsilon_pos r.anchor₁ r.anchor₂ r.anchors_distinct))
  have heps0 : Tendsto eps atTop (𝓝 0) :=
    ZWSystem.epsilon_tendsto_zero_of_inverseScale q r.vanishing
  have hsmall (a b : Fin 5) (ha : a ≠ v) (hb : b ≠ v) :
      (fun t => (q t).z a - (q t).z b) =O[atTop] eps ∧
      (fun t => (q t).w a - (q t).w b) =O[atTop] eps := by
    by_cases hab : a = b
    · subst b
      simpa only [sub_self] using And.intro (isBigO_zero eps atTop) (isBigO_zero eps atTop)
    · let p := ZWSystem.pairEstimateData q r.balanced a b hab
      exact p.small_separations_iff_double.mpr
        ⟨(r.leading.pair_z_stroke_iff r.balanced a b hab).mpr (hc a b ha hb hab).1,
         (r.leading.pair_w_stroke_iff r.balanced a b hab).mpr (hc a b ha hb hab).2⟩
  have hC : (∑ k ∈ Finset.univ.erase v, mass k) ≠ 0 :=
    hm _ ⟨j,Finset.mem_erase.mpr ⟨hj,Finset.mem_univ j⟩⟩
  have hex (k : Fin 5) (hk : k ≠ v) :
      (fun t => ((q t).delta v k)⁻¹ ^ 2) =O[atTop] (fun t => (eps t)⁻¹) :=
    r.orders.collapsing_complement_squared_radius_bound r.balanced v j hj hC
      (fun a b ha hb => (hsmall a b ha hb).1)
      (fun a b ha hb => (hsmall a b ha hb).2) k hk
  have hd (k : Fin 10) :
      (fun t => ((q t).delta (fiveBodyEdges k).1 (fiveBodyEdges k).2)⁻¹ ^ 2)
        =O[atTop] (fun t => fiveBodyClusterBound (eps t) v k) := by
    have hne := five_body_edge_distinct k
    by_cases h1 : (fiveBodyEdges k).1 = v
    · simpa only [fiveBodyClusterBound,fiveBodyEdgeTouches,h1,true_or,if_true] using
        hex (fiveBodyEdges k).2 (by simpa only [h1] using hne.symm)
    by_cases h2 : (fiveBodyEdges k).2 = v
    · have hh := hex (fiveBodyEdges k).1 h1
      simpa only [fiveBodyClusterBound,fiveBodyEdgeTouches,h2,or_true,if_true,
        (q _).delta_symm v] using hh
    · let p := ZWSystem.pairEstimateData q r.balanced (fiveBodyEdges k).1 (fiveBodyEdges k).2 hne
      have hr := p.double_force_iff_radius.mp
        ⟨(r.leading.pair_z_stroke_iff r.balanced _ _ hne).mpr (hc _ _ h1 h2 hne).1,
         (r.leading.pair_w_stroke_iff r.balanced _ _ hne).mpr (hc _ _ h1 h2 hne).2⟩
      simpa only [fiveBodyClusterBound,fiveBodyEdgeTouches,h1,h2,or_self,if_false] using hr.1.pow 2
  have hp : (fun t => (q t).fiveBodyFourProduct e) =O[atTop]
      (fun t => fiveBodyFourProducts (fiveBodyClusterBound (eps t) v) e) := by
    have hh := (hd e).mul ((hd (fiveBodyDisjointEdges e 0)).mul
      ((hd (fiveBodyDisjointEdges e 1)).mul (hd (fiveBodyDisjointEdges e 2))))
    apply hh.congr
    · intro t
      simp only [ZWSystem.fiveBodyFourProduct,fiveBodyFourProducts,Fin.prod_univ_succ]
      simp
    · intro t
      simp [fiveBodyFourProducts,Fin.prod_univ_succ]
  apply hp.trans_tendsto
  simp only [five_body_four_product_cluster_bound _ (heps _)]
  split_ifs
  · simpa only [zero_pow (by decide : 5 ≠ 0)] using heps0.pow 5
  · simpa only [zero_pow (by decide : 2 ≠ 0)] using heps0.pow 2

theorem four_product_not_escaping_of_four_body_clique
    (hm : AdmissibleMasses mass) (v j : Fin 5) (hj : j ≠ v)
    (hc : ∀ a b, a ≠ v → b ≠ v → a ≠ b →
      r.leading.z.force a b ≠ 0 ∧ r.leading.w.force a b ≠ 0) :
    ¬ FourProductEscapes r.sequence := by
  rintro ⟨e,he⟩
  have h := (r.four_product_tendsto_zero_of_four_body_clique hm v j hj hc e).norm
  exact not_tendsto_atTop_of_tendsto_nhds h he

end OrderedDiagramRealization

theorem five_body_source_complete_cluster :
    ∀ k ∈ ({1,14,15} : Finset (Fin 20)), ∀ a b : Fin 5,
      a ≠ 0 → b ≠ 0 → a ≠ b →
      (fiveBodySourceDiagram k).1 (upperIndex a b) = true ∧
      (fiveBodySourceDiagram k).2 (upperIndex a b) = true := by decide +kernel

theorem OrderedDiagramRealization.five_body_four_product_not_escaping_of_source
    {mass : Fin 5 → ℂ} {k : Fin 20}
    (r : OrderedDiagramRealization mass (fiveBodySourceDiagram k))
    (hm : AdmissibleMasses mass) (hk : k ∈ ({1,14,15} : Finset (Fin 20))) :
    ¬ FourProductEscapes r.sequence := by
  apply r.four_product_not_escaping_of_four_body_clique hm 0 1 (by decide)
  intro a b ha hb hab
  have h := five_body_source_complete_cluster k hk a b ha hb hab
  exact ⟨r.leading.z_force_ne_zero_of_code r.diagram_eq a b hab h.1,
    r.leading.w_force_ne_zero_of_code r.diagram_eq a b hab h.2⟩

end
end CentralConfigurations
