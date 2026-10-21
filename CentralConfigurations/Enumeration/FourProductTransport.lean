import CentralConfigurations.Asymptotics.FourProductDominance
import CentralConfigurations.Enumeration.FourBodyDominantEntry
import CentralConfigurations.Enumeration.OrderedDiagramRealization

/-! Transport of the selected four-product through balancing, relabeling,
color exchange, and the additional order extraction. -/

namespace CentralConfigurations
noncomputable section
open scoped BigOperators Topology
open Filter
attribute [local irreducible] DiagramCode.orbit
set_option maxRecDepth 10000

def fiveBodyFourProductEdgeList (e : Fin 10) : List (Fin 5 × Fin 5) :=
  [fiveBodyEdges e, fiveBodyEdges (fiveBodyDisjointEdges e 0),
    fiveBodyEdges (fiveBodyDisjointEdges e 1),fiveBodyEdges (fiveBodyDisjointEdges e 2)]

def orderedFiveBodyPair (p : Fin 5 × Fin 5) : Fin 5 × Fin 5 :=
  (min p.1 p.2,max p.1 p.2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem five_body_four_product_edges_relabel : ∀ σ : Equiv.Perm (Fin 5), ∀ e : Fin 10,
    ∃ k : Fin 10, ((fiveBodyFourProductEdgeList e).map (fun p =>
      orderedFiveBodyPair (σ p.1,σ p.2))).Perm (fiveBodyFourProductEdgeList k) := by decide +kernel

theorem five_body_four_product_list {R : Type*} [CommMonoid R]
    (d : Fin 5 → Fin 5 → R) (e : Fin 10) :
    ((fiveBodyFourProductEdgeList e).map (fun p => d p.1 p.2)).prod =
      fiveBodyFourProducts (fun k => d (fiveBodyEdges k).1 (fiveBodyEdges k).2) e := by
  simp [fiveBodyFourProductEdgeList,fiveBodyFourProducts,Fin.prod_univ_succ]

theorem symmetric_value_ordered_pair {R : Type*} (d : Fin 5 → Fin 5 → R)
    (hd : ∀ a b, d a b = d b a) (p : Fin 5 × Fin 5) :
    d (orderedFiveBodyPair p).1 (orderedFiveBodyPair p).2 = d p.1 p.2 := by
  by_cases h : p.1 ≤ p.2
  · simp [orderedFiveBodyPair,min_eq_left h,max_eq_right h]
  · have h' := le_of_lt (lt_of_not_ge h)
    simpa [orderedFiveBodyPair,min_eq_right h',max_eq_left h'] using hd p.2 p.1

theorem five_body_four_product_relabel {R : Type*} [CommMonoid R]
    (d : Fin 5 → Fin 5 → R) (hd : ∀ a b, d a b = d b a)
    (σ : Equiv.Perm (Fin 5)) (e : Fin 10) :
    ∃ k : Fin 10,
      fiveBodyFourProducts (fun v => d (σ (fiveBodyEdges v).1) (σ (fiveBodyEdges v).2)) e =
        fiveBodyFourProducts (fun v => d (fiveBodyEdges v).1 (fiveBodyEdges v).2) k := by
  obtain ⟨k,hk⟩ := five_body_four_product_edges_relabel σ e
  refine ⟨k,?_⟩
  have h := (hk.map (fun p => d p.1 p.2)).prod_eq
  simpa only [List.map_map,Function.comp_def,symmetric_value_ordered_pair d hd,
    five_body_four_product_list] using h

def ZWSystem.fiveBodyFourProduct {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) (e : Fin 10) : ℂ :=
  fiveBodyFourProducts (fun k => ((q.delta (fiveBodyEdges k).1 (fiveBodyEdges k).2)⁻¹)^2) e

theorem NormalizedSystem.five_body_four_product_toZW {mass : Fin 5 → ℂ}
    (q : NormalizedSystem ℂ 5 mass) (e : Fin 10) :
    q.toZW.fiveBodyFourProduct e = q.fiveBodyFourProduct e := by
  unfold ZWSystem.fiveBodyFourProduct NormalizedSystem.fiveBodyFourProduct
  congr 1
  funext k
  exact q.inverse_distance_squared (five_body_edge_distinct k)

def FourProductEscapes {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass) : Prop :=
  ∃ e : Fin 10, Tendsto (fun t => ‖(q t).fiveBodyFourProduct e‖) atTop atTop

theorem FourProductEscapes.comp {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
    (h : FourProductEscapes q) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    FourProductEscapes (q ∘ φ) := by
  obtain ⟨e,he⟩ := h
  exact ⟨e,he.comp hφ⟩

theorem FourProductEscapes.swap {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
    (h : FourProductEscapes q) : FourProductEscapes (fun t => (q t).swap) := h

theorem FourProductEscapes.relabel {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
    (h : FourProductEscapes q) (σ : Equiv.Perm (Fin 5)) :
    FourProductEscapes (fun t => (q t).relabel σ) := by
  obtain ⟨e,he⟩ := h
  obtain ⟨k,hk⟩ := five_body_four_product_edges_relabel σ.symm e
  have hv (t) : ((q t).relabel σ).fiveBodyFourProduct k = (q t).fiveBodyFourProduct e := by
    let d := fun a b => (((q t).relabel σ).delta a b)⁻¹ ^ 2
    have hd (a b) : d a b = d b a := by
      dsimp [d]
      rw [((q t).relabel σ).delta_symm]
    have h := (hk.map (fun p => d p.1 p.2)).prod_eq
    have h' := (show fiveBodyFourProducts (fun v => d (σ.symm (fiveBodyEdges v).1)
        (σ.symm (fiveBodyEdges v).2)) e =
        fiveBodyFourProducts (fun v => d (fiveBodyEdges v).1 (fiveBodyEdges v).2) k from by
      simpa only [List.map_map,Function.comp_def,symmetric_value_ordered_pair d hd,
        five_body_four_product_list] using h)
    simpa [d,ZWSystem.relabel,ZWSystem.fiveBodyFourProduct] using h'.symm
  exact ⟨k,he.congr (fun t => congrArg norm (hv t).symm)⟩

theorem exists_ordered_realization_with_escaping_four_product {mass : Fin 5 → ℂ}
    (q : ℕ → ZWSystem ℂ 5 mass)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j : Fin 5) (hij : i ≠ j)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) (he : FourProductEscapes q) :
    ∃ r : OrderedDiagramRealization mass l.diagramCode, FourProductEscapes r.sequence := by
  obtain ⟨φ,hφ,⟨o⟩⟩ := exists_sequenceOrderAssignment q hb i j hij ha
  exact ⟨{
    sequence := q ∘ φ
    balanced := fun t => hb (φ t)
    anchor₁ := i
    anchor₂ := j
    anchors_distinct := hij
    vanishing := ha.comp hφ.tendsto_atTop
    leading := l.comp φ hφ.tendsto_atTop
    z_nonzero := hz
    w_nonzero := hw
    diagram_eq := rfl
    orders := o
  },he.comp φ hφ.tendsto_atTop⟩

theorem ordered_realization_of_mem_orbit_with_escaping_four_product
    {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j : Fin 5) (hij : i ≠ j)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) (he : FourProductEscapes q)
    {d : DiagramCode 5} (hd : d ∈ DiagramCode.orbit l.diagramCode) :
    ∃ e : Equiv.Perm (Fin 5), ∃ r : OrderedDiagramRealization (fun k => mass (e k)) d,
      FourProductEscapes r.sequence := by
  obtain ⟨e,flip,hcode⟩ := (DiagramCode.mem_orbit_iff _ _).mp hd
  let qr := fun t => (q t).relabel e
  let lr := l.relabelCanonical e
  have hbr : ∀ t, ‖(qr t).zVector‖ = ‖(qr t).wVector‖ := by
    simpa only [qr,ZWSystem.zVector_norm_relabel,ZWSystem.wVector_norm_relabel] using hb
  have har : Tendsto (fun t => (qr t).inverseScale) atTop (𝓝 0) := by
    simpa only [qr,ZWSystem.inverseScale_relabel] using ha
  have hijr : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
  have hzr : lr.z.Nonzero := (l.z.nonzero_relabel_iff e).mpr hz
  have hwr : lr.w.Nonzero := (l.w.nonzero_relabel_iff e).mpr hw
  have her : FourProductEscapes qr := he.relabel e
  refine ⟨e,?_⟩
  cases flip
  · have hdiagram : lr.diagramCode = d := by
      rw [show lr.diagramCode = DiagramCode.relabel l.diagramCode e from l.diagramCode_relabelCanonical e]
      simpa only [DiagramCode.transform,Bool.false_eq_true,if_false] using hcode
    rw [← hdiagram]
    exact exists_ordered_realization_with_escaping_four_product qr hbr
      (e.symm i) (e.symm j) hijr har lr hzr hwr her
  · have has : Tendsto (fun t => ((qr t).swap).inverseScale) atTop (𝓝 0) := by
      change Tendsto (fun t => (‖(qr t).wVector‖ : ℂ)⁻¹) atTop (𝓝 0)
      simpa only [ZWSystem.inverseScale,← hbr] using har
    have hdiagram : (lr.swapBalanced hbr).diagramCode = d := by
      change DiagramCode.swap (l.relabelCanonical e).diagramCode = d
      rw [l.diagramCode_relabelCanonical e]
      simpa only [DiagramCode.transform,if_true] using hcode
    rw [← hdiagram]
    exact exists_ordered_realization_with_escaping_four_product
      (fun t => (qr t).swap) (fun t => (hbr t).symm)
      (e.symm i) (e.symm j) hijr has (lr.swapBalanced hbr) hwr hzr her.swap

end
end CentralConfigurations
