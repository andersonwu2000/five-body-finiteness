import CentralConfigurations.FiveBody.OrdinaryD7Metric
import CentralConfigurations.FiveBody.PhysicalPotentialFloor

/-!
# D7 exclusion at a four-product pole

On a fixed nonzero complex potential level, a D7 degeneration cannot carry
a pole of an original four-product. This applies in particular to every
physical positive level; it does not exclude all D7 degenerations.
-/

namespace CentralConfigurations.FiveBody.Ordinary.D7
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators

theorem shifted_potential {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) :
    q.toNormalized.unorderedPotential =
      (∑ i, mass i * ((q.z i-q.z 4)*(q.w i-q.w 4))) -
        (∑ i, mass i) * q.z 4 * q.w 4 := by
  rw [← q.toNormalized.potential_eq_unordered, D5.zw_potential]
  have hz := q.mass_center_z
  have hw := q.mass_center_w
  simp [Fin.sum_univ_succ] at hz hw ⊢
  linear_combination q.w 4 * hz + q.z 4 * hw

theorem inverse_zero_of_norm_pole {f : ℕ → ℂ}
    (hp : Tendsto (fun t => ‖f t‖) atTop atTop) :
    Tendsto (fun t => (f t)⁻¹) atTop (𝓝 0) := by
  have h : (fun _ : ℕ => (1 : ℂ)) =o[atTop] f :=
    isLittleO_const_left.mpr (Or.inr hp)
  have hh := h.inv_rev (Eventually.of_forall (fun _ hzero => (one_ne_zero hzero).elim))
  exact (isLittleO_one_iff ℂ).mp (by simpa only [inv_one] using hh)

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
  (hd : l.diagramCode = akDiagram 6)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include hb hd ha

theorem wing_shifted_products_zero (i : Fin 5) :
    Tendsto (fun t => zsep q i 4 t * wsep q i 4 t) atTop (𝓝 0) := by
  by_cases hi : i ∈ ({0,1} : Finset (Fin 5))
  · have ho := (upper_orders l hb hd i hi).1.1.mul (upper_orders l hb hd i hi).2.1
    have hr := (upper_radius_zero l hb hd ha).pow 2
    simp only [zero_pow (by decide : 2 ≠ 0)] at hr
    have hh := ho.congr_right (fun t => ((ZWSystem.pairEstimateData q hb 0 1 (by decide)).radius_sq t).symm)
    exact (isLittleO_one_iff ℂ).mp (hh.trans_isLittleO ((isLittleO_one_iff ℂ).mpr hr))
  by_cases hi' : i ∈ ({2,3} : Finset (Fin 5))
  · have ho := (lower_orders l hb hd i hi').1.1.mul (lower_orders l hb hd i hi').2.1
    have hr := (lower_radius_zero l hb hd ha).pow 2
    simp only [zero_pow (by decide : 2 ≠ 0)] at hr
    have hh := ho.congr_right (fun t => ((ZWSystem.pairEstimateData q hb 2 3 (by decide)).radius_sq t).symm)
    exact (isLittleO_one_iff ℂ).mp (hh.trans_isLittleO ((isLittleO_one_iff ℂ).mpr hr))
  · have hi4 : i = 4 := by fin_cases i <;> simp_all [Fin.ext_iff]
    subst i
    simpa only [zsep,wsep,sub_self,zero_mul] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))

theorem opposite_force_product_zero_of_pole (he : FourProductEscapes q) :
    Tendsto (fun t => upperOppForce q t * lowerOppForce q t) atTop (𝓝 0) := by
  obtain ⟨e,he⟩ := he
  have hinv := inverse_zero_of_norm_pole he
  have hne (t) : (q t).fiveBodyFourProduct e ≠ 0 := by
    simp only [ZWSystem.fiveBodyFourProduct, fiveBodyFourProducts]
    apply mul_ne_zero
    · exact pow_ne_zero 2 (inv_ne_zero ((q t).delta_ne_zero _ _ (five_body_edge_distinct e)))
    · apply Finset.prod_ne_zero_iff.mpr
      intro k _
      exact pow_ne_zero 2 (inv_ne_zero ((q t).delta_ne_zero _ _ (five_body_edge_distinct _)))
  have hh := (fourProduct_bigO_poleModel l hb hd ha e).inv_rev
    (Eventually.of_forall (fun t ht => (hne t ht).elim))
  have hmodel := (isLittleO_one_iff ℂ).mp
    (hh.trans_isLittleO ((isLittleO_one_iff ℂ).mpr hinv))
  apply tendsto_zero_of_complex_power (by decide : (2 : ℕ) ≠ 0)
  apply hmodel.congr
  intro t
  have h := poleModel_reciprocal hb t
  have hne' : poleModel q t ≠ 0 := by intro hz; rw [hz,mul_zero] at h; exact zero_ne_one h
  apply mul_right_cancel₀ hne'
  simpa only [inv_mul_cancel₀ hne'] using h.symm

theorem potential_zero_of_pole (hmu : mass 0 + mass 1 ≠ 0)
    (hml : mass 2 + mass 3 ≠ 0) (he : FourProductEscapes q) :
    Tendsto (fun t => (q t).toNormalized.unorderedPotential) atTop (𝓝 0) := by
  have hterms := tendsto_finsetSum Finset.univ (fun i _ =>
    (wing_shifted_products_zero l hb hd ha i).const_mul (mass i))
  simp only [mul_zero,Finset.sum_const_zero] at hterms
  have hcenter := (center_z_bound l hb hd ha hml).mul (center_w_bound l hb hd ha hmu)
  have hAB := (opposite_force_product_zero_of_pole l hb hd ha he).congr
    (fun t => mul_comm (upperOppForce q t) (lowerOppForce q t))
  have hc := (isLittleO_one_iff ℂ).mp
    (hcenter.trans_isLittleO ((isLittleO_one_iff ℂ).mpr hAB))
  have hh := hterms.sub (hc.const_mul (∑ i, mass i))
  simp only [mul_zero,sub_zero] at hh
  exact hh.congr (fun t => by rw [shifted_potential]; dsimp [zsep,wsep]; ring)

theorem not_escaping_of_fixed_nonzero_potential (hmu : mass 0 + mass 1 ≠ 0)
    (hml : mass 2 + mass 3 ≠ 0) {c : ℂ} (hc : c ≠ 0)
    (hlevel : ∀ t, (q t).toNormalized.unorderedPotential = c) :
    ¬ FourProductEscapes q := by
  intro he
  have hz := potential_zero_of_pole l hb hd ha hmu hml he
  have hconst : Tendsto (fun t => (q t).toNormalized.unorderedPotential) atTop (𝓝 c) :=
    tendsto_const_nhds.congr (fun t => (hlevel t).symm)
  exact hc (tendsto_nhds_unique hconst hz)

omit l hb hd ha in
theorem not_escaping_of_physical_potential {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0 < m i) (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (hd : l.diagramCode = akDiagram 6)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hlevel : ∀ t, (q t).toNormalized.unorderedPotential = (I0 : ℂ)) :
    ¬ FourProductEscapes q := by
  apply not_escaping_of_fixed_nonzero_potential l hb hd ha
    (by exact_mod_cast ne_of_gt (add_pos (hm 0) (hm 1)))
    (by exact_mod_cast ne_of_gt (add_pos (hm 2) (hm 3)))
    (by exact_mod_cast ne_of_gt hphysical.1) hlevel

end
end CentralConfigurations.FiveBody.Ordinary.D7
