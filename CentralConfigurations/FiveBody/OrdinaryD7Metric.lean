import CentralConfigurations.FiveBody.OrdinaryD7Response
import CentralConfigurations.FiveBody.OrdinaryTwoTriangleBounds
import CentralConfigurations.FiveBody.D5PositionLimits

/-! D7 metric decay and the exact reciprocal identity controlling original
four-product poles. No complex root or unsigned-sheet convention is used. -/

namespace CentralConfigurations.FiveBody.Ordinary.D7
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators

theorem center_w_identity {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) :
    (mass 0 + mass 1) * q.w 4 =
      -(mass 4 * (mass 0 * q.wForce 4 0 + mass 1 * q.wForce 4 1)) +
      (mass 0 * mass 2 * q.wForce 0 2 + mass 0 * mass 3 * q.wForce 0 3 +
       mass 1 * mass 2 * q.wForce 1 2 + mass 1 * mass 3 * q.wForce 1 3) -
      mass 0 * (q.w 0 - q.w 4) - mass 1 * (q.w 1 - q.w 4) := by
  have h2 := q.force_w 2
  have h3 := q.force_w 3
  have h4 := q.force_w 4
  have hc := q.mass_center_w
  simp [Fin.sum_univ_succ, q.delta_diagonal] at h2 h3 h4 hc
  dsimp [ZWSystem.wForce]
  rw [q.delta_symm 2 0, q.delta_symm 2 1] at h2
  rw [q.delta_symm 3 0, q.delta_symm 3 1, q.delta_symm 3 2] at h3
  rw [q.delta_symm 4 2, q.delta_symm 4 3] at h4
  linear_combination hc - mass 2 * h2 - mass 3 * h3 - mass 4 * h4

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
  (hd : l.diagramCode = akDiagram 6)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include hb hd ha

theorem center_w_bound (hmu : mass 0 + mass 1 ≠ 0) :
    (fun t => (q t).w 4) =O[atTop] upperOppForce q := by
  have hf0 := (upper_internal_force_bound l hb hd ha 0 (by decide)).neg_left
  have hf1 := (upper_internal_force_bound l hb hd ha 1 (by decide)).neg_left
  have hf0' : (fun t => (q t).wForce 4 0) =O[atTop] upperOppForce q :=
    hf0.congr_left (fun t => ((q t).swap.zForce_antisymm 4 0).symm)
  have hf1' : (fun t => (q t).wForce 4 1) =O[atTop] upperOppForce q :=
    hf1.congr_left (fun t => ((q t).swap.zForce_antisymm 4 1).symm)
  have hB := ((hf0'.const_mul_left (mass 0)).add (hf1'.const_mul_left (mass 1))).const_mul_left (mass 4)
  have hC := (((cross_wForce_bound l hb hd ha 0 2 (by decide) (by decide)).const_mul_left (mass 0 * mass 2)).add
    ((cross_wForce_bound l hb hd ha 0 3 (by decide) (by decide)).const_mul_left (mass 0 * mass 3))).add
    (((cross_wForce_bound l hb hd ha 1 2 (by decide) (by decide)).const_mul_left (mass 1 * mass 2)).add
    ((cross_wForce_bound l hb hd ha 1 3 (by decide) (by decide)).const_mul_left (mass 1 * mass 3)))
  have h0 := (upper_w_separation_force_bound l hb hd ha 0 (by decide)).const_mul_left (mass 0)
  have h1 := (upper_w_separation_force_bound l hb hd ha 1 (by decide)).const_mul_left (mass 1)
  have hh := ((hB.neg_left.add hC).sub h0).sub h1
  apply (isBigO_const_mul_left_iff hmu).mp
  exact hh.congr_left (fun t => by rw [center_w_identity]; dsimp [wsep]; ring)

theorem upper_radius_zero : Tendsto (radius q 0 1) atTop (𝓝 0) := by
  have hz := upper_z_force l hb hd 0 1 (by decide) (by decide) (by decide)
  have hpos := (l.z_position 0).sub (l.z_position 1)
  rw [l.z_position_zero_of_code hd 0 (no_circles 0).1,
    l.z_position_zero_of_code hd 1 (no_circles 1).1, sub_self] at hpos
  have h := hpos.div (l.z_force 0 1) hz
  simp only [zero_div] at h
  apply tendsto_zero_of_complex_power (by decide : (3 : ℕ) ≠ 0)
  convert h using 1
  funext t
  dsimp [radius, ZWSystem.zForce]
  field_simp [(q t).delta_ne_zero 0 1 (by decide),
    (q t).z_separation_ne_zero (by decide : (0 : Fin 5) ≠ 1),
    CentralConfigurations.ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t]

theorem lower_radius_zero : Tendsto (radius q 2 3) atTop (𝓝 0) := by
  have hw := lower_w_force l hb hd 2 3 (by decide) (by decide) (by decide)
  have hpos := (l.w_position 2).sub (l.w_position 3)
  rw [l.w_position_zero_of_code hd 2 (no_circles 2).2,
    l.w_position_zero_of_code hd 3 (no_circles 3).2, sub_self] at hpos
  have h := hpos.div (l.w_force 2 3) hw
  simp only [zero_div] at h
  apply tendsto_zero_of_complex_power (by decide : (3 : ℕ) ≠ 0)
  convert h using 1
  funext t
  dsimp [radius, ZWSystem.wForce]
  field_simp [(q t).delta_ne_zero 2 3 (by decide),
    (q t).w_separation_ne_zero (by decide : (2 : Fin 5) ≠ 3),
    CentralConfigurations.ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t]

def wingDistances (U V C : ℂ) : Fin 10 → ℂ := ![U,C,C,U,C,C,U,V,V,V]
def poleModel {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass) : ℕ → ℂ :=
  fun t => radius q 0 1 t ^ 2 * radius q 2 3 t ^ 2 * (zsep q 0 1 t * wsep q 2 3 t)^2

omit l hb hd ha in
theorem wing_fourProduct (U V C : ℂ) (e : Fin 10) :
    fiveBodyFourProducts (wingDistances U V C) e =
      if e = 0 then U * V^3 else if e = 7 then V * U^3 else U*V*C^2 := by
  fin_cases e <;> simp [wingDistances, fiveBodyFourProducts, fiveBodyDisjointEdges,
    Fin.prod_univ_succ, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.vecHead, Matrix.vecTail, Fin.ext_iff] <;> ring_nf <;> simp

theorem distance_wing_bounds (e : Fin 10) :
    (fun t => ((q t).delta (fiveBodyEdges e).1 (fiveBodyEdges e).2)⁻¹ ^ 2) =O[atTop]
      (fun t => wingDistances (radius q 0 1 t ^ 2) (radius q 2 3 t ^ 2)
        (zsep q 0 1 t * wsep q 2 3 t) e) := by
  have hu (i) (hi : i ∈ ({0,1} : Finset (Fin 5))) := (upper_orders l hb hd i hi).1.1.mul
    (upper_orders l hb hd i hi).2.1
  have hl (i) (hi : i ∈ ({2,3} : Finset (Fin 5))) := (lower_orders l hb hd i hi).1.1.mul
    (lower_orders l hb hd i hi).2.1
  have hc (i j) (hi : i ∈ ({0,1} : Finset (Fin 5))) (hj : j ∈ ({2,3} : Finset (Fin 5))) :=
    (cross_orders l hb hd ha i j hi hj).1.1.mul (cross_orders l hb hd ha i j hi hj).2.1
  have hmetric (i j : Fin 5) (hne : i ≠ j) (t) :
      ((q t).delta i j)⁻¹ ^ 2 = zsep q i j t * wsep q i j t :=
    (ZWSystem.pairEstimateData q hb i j hne).radius_sq t
  fin_cases e
  · exact isBigO_refl _ _
  · exact (hc 0 2 (by decide) (by decide)).congr_left (fun t => (hmetric 0 2 (by decide) t).symm)
  · exact (hc 0 3 (by decide) (by decide)).congr_left (fun t => (hmetric 0 3 (by decide) t).symm)
  · exact (hu 0 (by decide)).congr (fun t => (hmetric 0 4 (by decide) t).symm)
      (fun t => (hmetric 0 1 (by decide) t).symm)
  · exact (hc 1 2 (by decide) (by decide)).congr_left (fun t => (hmetric 1 2 (by decide) t).symm)
  · exact (hc 1 3 (by decide) (by decide)).congr_left (fun t => (hmetric 1 3 (by decide) t).symm)
  · exact (hu 1 (by decide)).congr (fun t => (hmetric 1 4 (by decide) t).symm)
      (fun t => (hmetric 0 1 (by decide) t).symm)
  · exact isBigO_refl _ _
  · exact (hl 2 (by decide)).congr (fun t => (hmetric 2 4 (by decide) t).symm)
      (fun t => (hmetric 2 3 (by decide) t).symm)
  · exact (hl 3 (by decide)).congr (fun t => (hmetric 3 4 (by decide) t).symm)
      (fun t => (hmetric 2 3 (by decide) t).symm)

theorem fourProduct_bigO_poleModel (e : Fin 10) :
    (fun t => (q t).fiveBodyFourProduct e) =O[atTop] poleModel q := by
  have hu := (upper_w_littleO_lower l hb hd ha 0 (by decide)).isBigO
  have hv := (lower_z_littleO_upper l hb hd ha 2 (by decide)).isBigO
  have hu' : (fun t => radius q 0 1 t ^ 2) =O[atTop]
      (fun t => zsep q 0 1 t * wsep q 2 3 t) := by
    have hh := (isBigO_refl (zsep q 0 1) atTop).mul ((upper_orders l hb hd 0 (by decide)).2.2.trans hu)
    exact hh.congr_left (fun t => ((ZWSystem.pairEstimateData q hb 0 1 (by decide)).radius_sq t).symm)
  have hv' : (fun t => radius q 2 3 t ^ 2) =O[atTop]
      (fun t => zsep q 0 1 t * wsep q 2 3 t) := by
    have hh := (((lower_orders l hb hd 2 (by decide)).1.2.trans hv)).mul (isBigO_refl (wsep q 2 3) atTop)
    exact hh.congr_left (fun t => ((ZWSystem.pairEstimateData q hb 2 3 (by decide)).radius_sq t).symm)
  have hbds := distance_wing_bounds l hb hd ha
  have hp := (hbds e).mul ((hbds (fiveBodyDisjointEdges e 0)).mul
    ((hbds (fiveBodyDisjointEdges e 1)).mul (hbds (fiveBodyDisjointEdges e 2))))
  have hh : (fun t => (q t).fiveBodyFourProduct e) =O[atTop]
      (fun t => fiveBodyFourProducts (wingDistances (radius q 0 1 t ^ 2)
        (radius q 2 3 t ^ 2) (zsep q 0 1 t * wsep q 2 3 t)) e) := by
    apply hp.congr
    · intro t
      simp only [ZWSystem.fiveBodyFourProduct, fiveBodyFourProducts, Fin.prod_univ_three]
      ring
    · intro t
      simp only [fiveBodyFourProducts, Fin.prod_univ_three]
      ring
  apply hh.trans
  simp only [wing_fourProduct]
  split_ifs
  · have hh := (isBigO_refl (fun t => radius q 0 1 t ^ 2 * radius q 2 3 t ^ 2) atTop).mul (hv'.pow 2)
    exact hh.congr_left (fun t => by ring)
  · have hh := (isBigO_refl (fun t => radius q 0 1 t ^ 2 * radius q 2 3 t ^ 2) atTop).mul (hu'.pow 2)
    exact hh.congr_left (fun t => by ring)
  · exact isBigO_refl _ _

omit l hb hd ha in
theorem poleModel_reciprocal (hb' : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (t : ℕ) :
    (upperOppForce q t * lowerOppForce q t)^2 * poleModel q t = 1 := by
  have hu := (q t).distance 0 1 (by decide)
  have hv := (q t).distance 2 3 (by decide)
  have hU : radius q 0 1 t ^ 2 = zsep q 0 1 t * wsep q 0 1 t :=
    (ZWSystem.pairEstimateData q hb' 0 1 (by decide)).radius_sq t
  have hV : radius q 2 3 t ^ 2 = zsep q 2 3 t * wsep q 2 3 t :=
    (ZWSystem.pairEstimateData q hb' 2 3 (by decide)).radius_sq t
  dsimp only [poleModel]
  rw [hU,hV]
  dsimp [upperOppForce,lowerOppForce,zsep,wsep,ZWSystem.zForce,ZWSystem.wForce]
  calc
    _ = ((q t).delta 0 1 ^ 2 * (((q t).z 0 - (q t).z 1) * ((q t).w 0 - (q t).w 1)))^3 *
        ((q t).delta 2 3 ^ 2 * (((q t).z 2 - (q t).z 3) * ((q t).w 2 - (q t).w 3)))^3 := by ring
    _ = 1 := by rw [hu,hv]; norm_num

end
end CentralConfigurations.FiveBody.Ordinary.D7
