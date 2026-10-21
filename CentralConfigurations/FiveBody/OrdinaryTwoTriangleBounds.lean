import CentralConfigurations.FiveBody.OrdinaryDiagramIdentity
import CentralConfigurations.Enumeration.FourProductTransport

/-! D10--D13: direct bounds on all ten original four-products from actual
stroke estimates, with no assumed AK order table or physical invariant. -/

namespace CentralConfigurations.FiveBody.Ordinary
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators

def twoTriangleDistanceBound (eps : ℂ) : Fin 10 → ℂ :=
  ![eps^2, eps⁻¹, eps⁻¹, eps^2, eps⁻¹, eps⁻¹, eps^2, 1, 1, 1]

theorem twoTriangle_fourProduct_bound (eps : ℂ) (hne : eps ≠ 0) (e : Fin 10) :
    fiveBodyFourProducts (twoTriangleDistanceBound eps) e =
      if e = 0 then eps^2 else if e = 7 then eps^6 else 1 := by
  fin_cases e <;>
    simp [fiveBodyFourProducts, twoTriangleDistanceBound, fiveBodyDisjointEdges,
      Fin.prod_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail, Fin.ext_iff] <;> field_simp [hne]

theorem d10_d13_w_star : ∀ d ∈ ({9,10,11,12} : Finset (Fin 16)), ∀ i : Fin 5, i ≠ 4 →
    (akDiagram d).2 (upperIndex i 4) = true := by decide +kernel

theorem d10_d13_double_edges : ∀ d ∈ ({9,10,11,12} : Finset (Fin 16)),
    ∀ e ∈ ({0,3,6} : Finset (Fin 10)),
    (akDiagram d).1 (upperIndex (fiveBodyEdges e).1 (fiveBodyEdges e).2) = true ∧
    (akDiagram d).2 (upperIndex (fiveBodyEdges e).1 (fiveBodyEdges e).2) = true := by
  decide +kernel

theorem d10_d13_lower_edges : ∀ d ∈ ({9,10,11,12} : Finset (Fin 16)),
    ∀ e ∈ ({7,8,9} : Finset (Fin 10)),
    (akDiagram d).2 (upperIndex (fiveBodyEdges e).1 (fiveBodyEdges e).2) = true := by
  decide +kernel

theorem not_norm_atTop_of_bigO_one {f : ℕ → ℂ}
    (hf : f =O[atTop] (fun _ => (1 : ℂ))) :
    ¬ Tendsto (fun t => ‖f t‖) atTop atTop := by
  intro hp
  obtain ⟨C, hC, hbound⟩ := hf.exists_pos
  obtain ⟨t, ht, hp⟩ := (hbound.bound.and (hp.eventually (eventually_gt_atTop C))).exists
  simp only [norm_one, mul_one] at ht
  linarith

namespace ScaledZWLimit
variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
  (l : CentralConfigurations.ScaledZWLimit q (fun t => (q t).inverseScale))
  (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
  {d : Fin 16} (hd : l.diagramCode = akDiagram d)
  (hk : d ∈ ({9,10,11,12} : Finset (Fin 16)))
include hb hd hk

theorem d10_d13_z_separation_bound (i j : Fin 5) :
    (fun t => (q t).z i - (q t).z j) =O[atTop] (fun t => ((q t).epsilon : ℂ)) := by
  have hs (a : Fin 5) :
      (fun t => (q t).z a - (q t).z 4) =O[atTop] (fun t => ((q t).epsilon : ℂ)) := by
    by_cases ha : a = 4
    · subst a
      simpa only [sub_self] using isBigO_zero (fun t => ((q t).epsilon : ℂ)) atTop
    · let p := ZWSystem.pairEstimateData q hb a 4 ha
      have hw := l.w_force_ne_zero_of_code hd a 4 ha (d10_d13_w_star d hk a ha)
      exact p.swap.stroke_w_upper ((l.pair_w_stroke_iff hb a 4 ha).mpr hw)
  exact ((hs i).sub (hs j)).congr_left (fun t => by ring)

theorem d10_d13_distance_bounds (e : Fin 10) :
    (fun t => ((q t).delta (fiveBodyEdges e).1 (fiveBodyEdges e).2)⁻¹ ^ 2) =O[atTop]
      (fun t => twoTriangleDistanceBound ((q t).epsilon : ℂ) e) := by
  let i := (fiveBodyEdges e).1
  let j := (fiveBodyEdges e).2
  have hij : i ≠ j := five_body_edge_distinct e
  let p := ZWSystem.pairEstimateData q hb i j hij
  by_cases hdouble : e ∈ ({0,3,6} : Finset (Fin 10))
  · have hforce := d10_d13_double_edges d hk e hdouble
    have hz := l.z_force_ne_zero_of_code hd i j hij hforce.1
    have hw := l.w_force_ne_zero_of_code hd i j hij hforce.2
    have hr := (p.double_force_iff_radius.mp
      ⟨(l.pair_z_stroke_iff hb i j hij).mpr hz, (l.pair_w_stroke_iff hb i j hij).mpr hw⟩).1.pow 2
    convert hr using 1
    funext t
    have he : e = 0 ∨ e = 3 ∨ e = 6 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hdouble
    rcases he with rfl | rfl | rfl <;> rfl
  by_cases hlower : e ∈ ({7,8,9} : Finset (Fin 10))
  · have hw := l.w_force_ne_zero_of_code hd i j hij (d10_d13_lower_edges d hk e hlower)
    have hr := (p.swap.stroke_radius_upper ((l.pair_w_stroke_iff hb i j hij).mpr hw)).pow 2
    convert hr using 1
    funext t
    have he : e = 7 ∨ e = 8 ∨ e = 9 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hlower
    rcases he with rfl | rfl | rfl <;> change (1 : ℂ) = 1^2 <;> norm_num
  · have hr := (d10_d13_z_separation_bound l hb hd hk i j).mul p.w_upper
    apply hr.congr
    · intro t
      exact (p.radius_sq t).symm
    · intro t
      have he : e = 1 ∨ e = 2 ∨ e = 4 ∨ e = 5 := by
        fin_cases e <;> simp_all [Fin.ext_iff]
      rcases he with rfl | rfl | rfl | rfl <;>
        change ((q t).epsilon : ℂ) * (((q t).epsilon : ℂ)⁻¹ ^ 2) = ((q t).epsilon : ℂ)⁻¹ <;>
        field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt ((q t).epsilon_pos 0 1 (by decide)))]

theorem d10_d13_fourProduct_bounded
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) (e : Fin 10) :
    (fun t => (q t).fiveBodyFourProduct e) =O[atTop] (fun _ => (1 : ℂ)) := by
  let eps := fun t => ((q t).epsilon : ℂ)
  have heps : Tendsto eps atTop (𝓝 0) := ZWSystem.epsilon_tendsto_zero_of_inverseScale q ha
  have hne (t) : eps t ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt ((q t).epsilon_pos 0 1 (by decide)))
  have hbds := d10_d13_distance_bounds l hb hd hk
  have hp := (hbds e).mul ((hbds (fiveBodyDisjointEdges e 0)).mul
    ((hbds (fiveBodyDisjointEdges e 1)).mul (hbds (fiveBodyDisjointEdges e 2))))
  have hh : (fun t => (q t).fiveBodyFourProduct e) =O[atTop]
      (fun t => fiveBodyFourProducts (twoTriangleDistanceBound (eps t)) e) := by
    apply hp.congr
    · intro t
      simp only [ZWSystem.fiveBodyFourProduct, fiveBodyFourProducts, Fin.prod_univ_three]
      ring
    · intro t
      simp only [fiveBodyFourProducts, Fin.prod_univ_three, eps]
      ring
  apply hh.trans
  simp only [twoTriangle_fourProduct_bound _ (hne _)]
  split_ifs
  · exact (heps.pow 2).isBigO_one ℂ
  · exact (heps.pow 6).isBigO_one ℂ
  · exact isBigO_refl _ _

theorem d10_d13_not_escaping
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    ¬ FourProductEscapes q := by
  rintro ⟨e, he⟩
  exact not_norm_atTop_of_bigO_one (d10_d13_fourProduct_bounded l hb hd hk ha e) he

end ScaledZWLimit
end
end CentralConfigurations.FiveBody.Ordinary
