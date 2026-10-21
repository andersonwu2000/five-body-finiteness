import CentralConfigurations.FiveBody.PairEnergyInertia

namespace CentralConfigurations.FiveBody.PairEnergy
open Filter Asymptotics
open scoped Topology BigOperators

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass} {b : Bool}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hd : l.diagramCode=akDiagram b)
include l hd

theorem cross_delta_zero (i j : Fin 5) (hi : i<2) (hj : 2 ≤ j) :
    Tendsto (fun t => (q t).delta i j) atTop (𝓝 0) := by
  have hpos : l.z.position i ≠ l.z.position j := by
    rw [triple_z_positions_zero l hd j hj]
    exact pair_z_positions_ne l hd i hi
  have h := l.swap.delta_cube_limit_of_w_positions_ne scale_ne i j hpos
  apply D9.zero_of_power (n := 3) (by decide)
  simpa only [ScaledZWLimit.swap,cross_z_force_zero l hd i j hi hj,zero_div] using h

theorem cross_w_force_div_scale_zero (i j : Fin 5) (hi : i<2) (hj : 2 ≤ j) :
    Tendsto (fun t => (q t).wForce i j / A q t) atTop (𝓝 0) := by
  have hij : i ≠ j := by omega
  have hpos : l.z.position i-l.z.position j ≠ 0 := by
    rw [triple_z_positions_zero l hd j hj,sub_zero]
    exact pair_z_positions_ne l hd i hi
  have h := (cross_delta_zero l hd i j hi hj).div ((l.z_position i).sub (l.z_position j)) hpos
  have heq t : (q t).delta i j / (A q t*(q t).z i-A q t*(q t).z j) =
      (q t).wForce i j/A q t := by
    rw [← mul_sub]
    dsimp [ZWSystem.wForce]
    field_simp [scale_ne (q := q) t,(q t).z_separation_ne_zero hij]
    linear_combination - (q t).delta i j * (q t).distance i j hij
  simpa only [zero_div] using h.congr heq

theorem triple_metric_zero (i j : Fin 5) (hi : 2 ≤ i) (hj : 2 ≤ j) (hij : i≠j) :
    Tendsto (D q i j) atTop (𝓝 0) := by
  have hf := triangle_w_force_ne l hd i j hi hj hij
  have h := ((l.w_position i).sub (l.w_position j)).div (l.w_force i j) hf
  have heq t : (A q t*(q t).w i-A q t*(q t).w j)/(A q t*(q t).wForce i j) =
      ((q t).delta i j)⁻¹^3 := by
    rw [← mul_sub]
    dsimp [ZWSystem.wForce]
    field_simp [scale_ne (q := q) t,delta_ne (q := q) i j hij t,(q t).w_separation_ne_zero hij]
  have hr : Tendsto (fun t => ((q t).delta i j)⁻¹) atTop (𝓝 0) := by
    apply D9.zero_of_power (n := 3) (by decide)
    simpa only [w_positions_zero l hd i,w_positions_zero l hd j,sub_self,zero_div] using h.congr heq
  simpa only [← metric_inv_delta i j hij,zero_pow (by decide : 2≠0)] using hr.pow 2

theorem pair_delta_cube_limit (hP : pairMass mass ≠ 0) :
    Tendsto (fun t => (q t).delta 0 1^3) atTop (𝓝 (pairMass mass)⁻¹) := by
  have hdiff : l.z.position 0-l.z.position 1=pairMass mass*l.z.force 0 1 := by
    rw [(pair_balances l hd).1,(pair_balances l hd).2]
    dsimp [pairMass]; ring
  have hpos : l.z.position 0 ≠ l.z.position 1 := by
    apply sub_ne_zero.mp
    rw [hdiff]
    exact mul_ne_zero hP (pair_force_ne l hd)
  have h := l.swap.delta_cube_limit_of_w_positions_ne scale_ne 0 1 hpos
  change Tendsto (fun t => (q t).delta 0 1^3) atTop
    (𝓝 (l.z.force 0 1/(l.z.position 0-l.z.position 1))) at h
  rw [hdiff] at h
  have he : l.z.force 0 1/(pairMass mass*l.z.force 0 1)=(pairMass mass)⁻¹ := by
    field_simp [hP,pair_force_ne l hd]
  rwa [he] at h

theorem pair_metric_cube_limit (hP : pairMass mass ≠ 0) :
    Tendsto (fun t => D q 0 1 t^3) atTop (𝓝 ((pairMass mass)^2)) := by
  have h := ((pair_delta_cube_limit l hd hP).inv₀ (inv_ne_zero hP)).pow 2
  simpa only [metric_inv_delta 0 1 (by decide),inv_pow,inv_inv,← pow_mul] using h

theorem pairZ_scaled_zero :
    Tendsto (fun t => A q t*pairZ (q t)) atTop (𝓝 0) := by
  have h := (((l.z_position 2).const_mul (mass 2)).add
    ((l.z_position 3).const_mul (mass 3))).add ((l.z_position 4).const_mul (mass 4))
  have heq t : -(mass 2*(A q t*(q t).z 2)+mass 3*(A q t*(q t).z 3)+
      mass 4*(A q t*(q t).z 4)) = A q t*pairZ (q t) := by
    have hc := (q t).mass_center_z
    simp [Fin.sum_univ_succ] at hc
    dsimp [pairZ]
    linear_combination -(A q t)*hc
  simpa only [triple_z_positions_zero l hd 2 (by decide),triple_z_positions_zero l hd 3 (by decide),
    triple_z_positions_zero l hd 4 (by decide),mul_zero,add_zero,neg_zero] using h.neg.congr heq

theorem pairW_div_scale_zero :
    Tendsto (fun t => pairW (q t)/A q t) atTop (𝓝 0) := by
  have h02 := (cross_w_force_div_scale_zero l hd 0 2 (by decide) (by decide)).const_mul (mass 0*mass 2)
  have h03 := (cross_w_force_div_scale_zero l hd 0 3 (by decide) (by decide)).const_mul (mass 0*mass 3)
  have h04 := (cross_w_force_div_scale_zero l hd 0 4 (by decide) (by decide)).const_mul (mass 0*mass 4)
  have h12 := (cross_w_force_div_scale_zero l hd 1 2 (by decide) (by decide)).const_mul (mass 1*mass 2)
  have h13 := (cross_w_force_div_scale_zero l hd 1 3 (by decide) (by decide)).const_mul (mass 1*mass 3)
  have h14 := (cross_w_force_div_scale_zero l hd 1 4 (by decide) (by decide)).const_mul (mass 1*mass 4)
  have h := ((((h02.add h03).add h04).add h12).add h13).add h14
  have heq t : mass 0*mass 2*((q t).wForce 0 2/A q t)+mass 0*mass 3*((q t).wForce 0 3/A q t)+
      mass 0*mass 4*((q t).wForce 0 4/A q t)+mass 1*mass 2*((q t).wForce 1 2/A q t)+
      mass 1*mass 3*((q t).wForce 1 3/A q t)+mass 1*mass 4*((q t).wForce 1 4/A q t) =
      pairW (q t)/A q t := by rw [pairW_boundary]; ring
  simpa only [mul_zero,add_zero] using h.congr heq

theorem pair_center_product_zero :
    Tendsto (fun t => pairZ (q t)*pairW (q t)) atTop (𝓝 0) := by
  have h := (pairZ_scaled_zero l hd).mul (pairW_div_scale_zero l hd)
  have heq t : (A q t*pairZ (q t))*(pairW (q t)/A q t)=pairZ (q t)*pairW (q t) := by
    field_simp [scale_ne (q := q) t]
  simpa only [mul_zero] using h.congr heq

theorem triple_metric_residual_zero :
    Tendsto (fun t => tripleMetric (q t)) atTop (𝓝 0) := by
  have h := (((triple_metric_zero l hd 2 3 (by decide) (by decide) (by decide)).const_mul (mass 2*mass 3)).add
    ((triple_metric_zero l hd 2 4 (by decide) (by decide) (by decide)).const_mul (mass 2*mass 4))).add
    ((triple_metric_zero l hd 3 4 (by decide) (by decide) (by decide)).const_mul (mass 3*mass 4))
  simpa only [tripleMetric,D,mul_zero,add_zero] using h

/-- The triple centroid product is controlled independently in the final
energy bookkeeping by the exact total-centroid identities. -/
theorem triple_center_product_zero :
    Tendsto (fun t => tripleZ (q t)*tripleW (q t)) atTop (𝓝 0) := by
  simpa only [tripleZ_eq_neg_pairZ,tripleW_eq_neg_pairW,neg_mul_neg] using pair_center_product_zero l hd

theorem both_centroid_products_zero :
    Tendsto (fun t => (pairZ (q t)/pairMass mass)*(pairW (q t)/pairMass mass)) atTop (𝓝 0) ∧
    Tendsto (fun t => (tripleZ (q t)/tripleMass mass)*(tripleW (q t)/tripleMass mass)) atTop (𝓝 0) := by
  constructor
  · simpa only [div_mul_div_comm,zero_div] using
      (pair_center_product_zero l hd).div_const (pairMass mass*pairMass mass)
  · simpa only [div_mul_div_comm,zero_div] using
      (triple_center_product_zero l hd).div_const (tripleMass mass*tripleMass mass)

end CentralConfigurations.FiveBody.PairEnergy
