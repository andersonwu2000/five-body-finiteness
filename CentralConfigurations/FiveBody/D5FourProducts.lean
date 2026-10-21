import CentralConfigurations.FiveBody.D5CanonicalMetric

namespace CentralConfigurations.FiveBody.D5
open Filter Asymptotics
open scoped Topology BigOperators

theorem one_internal_three_external {e a b c d : ℕ → ℂ} (he : ∀ t, e t≠0)
    (ha : a =O[atTop] (fun t => e t^2))
    (hb : b =o[atTop] (fun t => (e t)⁻¹))
    (hc : c =o[atTop] (fun t => (e t)⁻¹))
    (hd : d =o[atTop] (fun t => (e t)⁻¹)) :
    (fun t => a t*b t*c t*d t) =o[atTop] (fun t => (e t)⁻¹) := by
  have hh := ((ha.mul_isLittleO hb).mul_isBigO hc.isBigO).mul_isBigO hd.isBigO
  convert hh using 1
  funext t
  field_simp [he t]

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (hd : l.diagramCode=fiveBodySourceDiagram 2)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
  {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
  (hI : ∀ t, (q t).toNormalized.potential=(I0:ℂ))
include l hm hb hd ha hphysical hI

theorem canonical_edge_small (e : Fin 10) :
    edgeMetric q e =o[atTop] (fun t => (eps q t)⁻¹) :=
  metric_small_of_chang3 l hm hb hd ha hphysical hI _ _

omit hm ha hphysical hI in
theorem canonical_internal_edge_bigO (e : Fin 10) (he : e=7 ∨ e=8 ∨ e=9) :
    edgeMetric q e =O[atTop] (fun t => eps q t^2) := by
  apply internal_metric_bigO_of_chang3 l hb hd
  · rcases he with rfl | rfl | rfl <;> decide
  · rcases he with rfl | rfl | rfl <;> decide

/-- The internal triangle 234 is indexed by its complementary edge 01,
which is index 0 in the original ten-product family. -/
theorem internal_fourProduct_small :
    (fun t => (q t).toNormalized.fiveBodyFourProduct 0) =o[atTop]
      (fun t => eps q t^5) := by
  have h0 := canonical_edge_small l hm hb hd ha hphysical hI 0
  have h7 := canonical_internal_edge_bigO l hb hd 7 (by simp)
  have h8 := canonical_internal_edge_bigO l hb hd 8 (by simp)
  have h9 := canonical_internal_edge_bigO l hb hd 9 (by simp)
  have hh := ((h0.mul_isBigO h7).mul_isBigO h8).mul_isBigO h9
  apply hh.congr
  · intro t
    rw [original_fourProduct]
    simp [fiveBodyFourProducts,fiveBodyDisjointEdges,Fin.prod_univ_succ]
    ring
  · intro t
    field_simp [eps_ne (q := q) t]

theorem other_fourProduct_small (e : Fin 10) (he : e≠0) :
    (fun t => (q t).toNormalized.fiveBodyFourProduct e) =o[atTop]
      (fun t => (eps q t)⁻¹) := by
  have hx := canonical_edge_small l hm hb hd ha hphysical hI
  have hi := canonical_internal_edge_bigO l hb hd
  have hcase (k a b c : Fin 10) (hk : k=7 ∨ k=8 ∨ k=9) :
      (fun t => edgeMetric q k t * edgeMetric q a t * edgeMetric q b t * edgeMetric q c t)
        =o[atTop] (fun t => (eps q t)⁻¹) :=
    one_internal_three_external eps_ne (hi k hk) (hx a) (hx b) (hx c)
  fin_cases e
  · exact (he rfl).elim
  · apply (hcase 9 1 5 6 (by simp)).congr_left
    intro t; rw [original_fourProduct]
    simp [fiveBodyFourProducts,fiveBodyDisjointEdges,Fin.prod_univ_succ]; ring
  · apply (hcase 8 2 4 6 (by simp)).congr_left
    intro t; rw [original_fourProduct]
    simp [fiveBodyFourProducts,fiveBodyDisjointEdges,Fin.prod_univ_succ]; ring
  · apply (hcase 7 3 4 5 (by simp)).congr_left
    intro t; rw [original_fourProduct]
    simp [fiveBodyFourProducts,fiveBodyDisjointEdges,Fin.prod_univ_succ]; ring
  · apply (hcase 9 4 2 3 (by simp)).congr_left
    intro t; rw [original_fourProduct]
    simp [fiveBodyFourProducts,fiveBodyDisjointEdges,Fin.prod_univ_succ]; ring
  · apply (hcase 8 5 1 3 (by simp)).congr_left
    intro t; rw [original_fourProduct]
    simp [fiveBodyFourProducts,fiveBodyDisjointEdges,Fin.prod_univ_succ]; ring
  · apply (hcase 7 6 1 2 (by simp)).congr_left
    intro t; rw [original_fourProduct]
    simp [fiveBodyFourProducts,fiveBodyDisjointEdges,Fin.prod_univ_succ]; ring
  · apply (hcase 7 0 3 6 (by simp)).congr_left
    intro t; rw [original_fourProduct]
    simp [fiveBodyFourProducts,fiveBodyDisjointEdges,Fin.prod_univ_succ]; ring
  · apply (hcase 8 0 2 5 (by simp)).congr_left
    intro t; rw [original_fourProduct]
    simp [fiveBodyFourProducts,fiveBodyDisjointEdges,Fin.prod_univ_succ]; ring
  · apply (hcase 9 0 1 4 (by simp)).congr_left
    intro t; rw [original_fourProduct]
    simp [fiveBodyFourProducts,fiveBodyDisjointEdges,Fin.prod_univ_succ]; ring

/-- Ready for the complete mass-only R-list product theorem. Both estimates
are little-o, including every other triple without any R-list pruning. -/
theorem original_fourProduct_orders :
    (fun t => (q t).toNormalized.fiveBodyFourProduct 0) =o[atTop]
      (fun t => (q t).epsilon^5) ∧
    ∀ e : Fin 10, e≠0 → (fun t => (q t).toNormalized.fiveBodyFourProduct e) =o[atTop]
      (fun t => (q t).epsilon⁻¹) := by
  constructor
  · have h := (internal_fourProduct_small l hm hb hd ha hphysical hI).norm_right
    simpa only [eps,norm_pow,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((q _).epsilon_pos 0 1 (by decide))] using h
  · intro e he
    have h := (other_fourProduct_small l hm hb hd ha hphysical hI e he).norm_right
    simpa only [eps,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos ((q _).epsilon_pos 0 1 (by decide))] using h

end CentralConfigurations.FiveBody.D5
