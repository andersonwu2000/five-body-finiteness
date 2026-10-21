import CentralConfigurations.FiveBody.Source18TriangleLimit

/-!
# The six-term pair/triangle torque certificate

This records the finite limiting system used in Albouy--Kaloshin,
Section 8.2. The triangle is an actual three-body ZW solution. All six
cross inverse distances are extracted together, with their square
equations and the full torque relation. No square-root branch is chosen.
This module does not perform the subsequent mass elimination.
-/

namespace CentralConfigurations
open Filter
open scoped Topology BigOperators

structure FiveBodySource18Certificate (mass : Fin 5 → ℝ) where
  triangle : ZWSystem ℂ 3 (fun i => (mass (i.castLE (by decide)) : ℂ))
  w_ne_zero : ∀ i, triangle.w i ≠ 0
  pairZ : Fin 2 → ℂ
  pairZ_ne_zero : ∀ p, pairZ p ≠ 0
  pair_balance : (mass 3 : ℂ) * pairZ 0 + mass 4 * pairZ 1 = 0
  cross : Fin 2 → Fin 3 → ℂ
  cross_square : ∀ p i, cross p i ^ 2 * (-(pairZ p * triangle.w i)) = 1
  cross_torque : (∑ p : Fin 2, ∑ i : Fin 3,
    (mass (Fin.natAdd 3 p) : ℂ) * mass (i.castLE (by decide)) * cross p i) = 0

theorem ZWSystem.five_body_pair_triangle_torque_zero {mass : Fin 5 → ℂ}
    (q : ZWSystem ℂ 5 mass) :
    (∑ p : Fin 2, ∑ i : Fin 3,
      mass (Fin.natAdd 3 p) * mass (i.castLE (by decide)) *
        q.torqueTerm (Fin.natAdd 3 p) (i.castLE (by decide))) = 0 := by
  have h := q.pair_torque_zero 3 4 (by decide)
  have hc : ({3,4} : Finset (Fin 5))ᶜ = {0,1,2} := by decide +kernel
  rw [hc] at h
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,
    Finset.mem_singleton,Fin.isValue,Fin.reduceEq,or_self,not_false_eq_true] at h
  simp [Fin.sum_univ_succ]
  linear_combination h

theorem ZWSystem.five_body_pair_triangle_normalized_torque_zero {mass : Fin 5 → ℂ}
    (q : ZWSystem ℂ 5 mass) (a : ℂ) :
    (∑ p : Fin 2, ∑ i : Fin 3,
      mass (Fin.natAdd 3 p) * mass (i.castLE (by decide)) *
        (q.delta (Fin.natAdd 3 p) (i.castLE (by decide)) / a) *
        q.torqueCorrection (Fin.natAdd 3 p) (i.castLE (by decide))) = 0 := by
  have h := q.five_body_pair_triangle_torque_zero
  simp [Fin.sum_univ_succ, ZWSystem.torqueTerm_eq] at h ⊢
  linear_combination a⁻¹ * h

theorem ScaledZWLimit.five_body_source18_certificate {mass : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun r => (mass r : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ r, 0 < mass r) (hd : l.diagramCode = fiveBodySourceDiagram 17)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    Nonempty (FiveBodySource18Certificate mass) := by
  obtain ⟨r,hrw,hr0,φ,hφ,_,_⟩ := l.five_body_source18_triangle_limit hm hd ha
  let e : Fin 3 → Fin 5 := fun i => i.castLE (by decide)
  let b : Fin 2 → Fin 5 := Fin.natAdd 3
  let U : Fin 2 → ℂ := fun p => l.z.position (b p)
  have hs := inverseScale_ne_zero (q := q) 0 1 (by decide)
  have hU (p : Fin 2) : U p ≠ 0 := by
    apply l.z_position_ne_zero_of_code hd
    fin_cases p <;> decide +kernel
  have hWb (p : Fin 2) : l.w.position (b p) = 0 := by
    apply l.w_position_zero_of_code hd
    fin_cases p <;> decide +kernel
  have hZe (i : Fin 3) : l.z.position (e i) = 0 := by
    apply l.z_position_zero_of_code hd
    fin_cases i <;> decide +kernel
  have hWe (i : Fin 3) : l.w.position (e i) ≠ 0 := by
    rw [← hrw i]
    exact hr0 i
  have hpair : (mass 3 : ℂ)*U 0 + mass 4*U 1 = 0 := by
    simpa [U,b] using l.z_component_balance_of_code hd {3,4} (by decide +kernel)
  have hsq (p : Fin 2) (i : Fin 3) :
      Tendsto (fun t => ((q (φ t)).delta (b p) (e i) /
        (q (φ t)).inverseScale)^2) atTop (𝓝 ((-(U p * r.w i))⁻¹)) := by
    have h := l.delta_div_scale_squared_limit hs (b p) (e i)
      (by rw [hZe i]; exact hU p) (by rw [hWb p]; exact (hWe i).symm)
    simpa only [hZe i,hWb p,sub_zero,zero_sub,mul_neg,hrw i] using h.comp hφ.tendsto_atTop
  let f : ℕ → (Fin 2 × Fin 3) → ℂ := fun t c =>
    (q (φ t)).delta (b c.1) (e c.2)/(q (φ t)).inverseScale
  obtain ⟨v,ψ,hψ,hv⟩ := exists_finite_coordinate_limits f
    (fun c => bounded_of_power_tendsto (by decide : (2 : ℕ) ≠ 0) (hsq c.1 c.2))
  let C : Fin 2 → Fin 3 → ℂ := fun p i => v (p,i)
  have hC (p : Fin 2) (i : Fin 3) : Tendsto
      (fun t => (q (φ (ψ t))).delta (b p) (e i)/(q (φ (ψ t))).inverseScale)
        atTop (𝓝 (C p i)) := hv (p,i)
  have hCsq (p : Fin 2) (i : Fin 3) : C p i ^ 2 * (-(U p * r.w i)) = 1 := by
    have h := tendsto_nhds_unique ((hC p i).pow 2) ((hsq p i).comp hψ.tendsto_atTop)
    rw [h, inv_mul_cancel₀ (neg_ne_zero.mpr (mul_ne_zero (hU p) (hr0 i)))]
  have hT (p : Fin 2) (i : Fin 3) : Tendsto
      (fun t => (q (φ (ψ t))).torqueCorrection (b p) (e i)) atTop (𝓝 (-1)) := by
    have hbi : b p ≠ e i := by fin_cases p <;> fin_cases i <;> decide +kernel
    exact ((l.opposite_position_torque_limit (b p) (e i) hbi (hU p)
      (hZe i) (hWb p) (hWe i)).comp hφ.tendsto_atTop).comp hψ.tendsto_atTop
  have hsum := tendsto_finsetSum Finset.univ (fun p _ =>
    tendsto_finsetSum Finset.univ (fun i _ =>
      ((hC p i).const_mul ((mass (b p) : ℂ)*mass (e i))).mul (hT p i)))
  have he (t : ℕ) := (q (φ (ψ t))).five_body_pair_triangle_normalized_torque_zero
    (q (φ (ψ t))).inverseScale
  have hz : (∑ p : Fin 2, ∑ i : Fin 3,
      (mass (b p) : ℂ)*mass (e i)*C p i*(-1)) = 0 := by
    apply tendsto_nhds_unique hsum
    simp only [show (fun t => ∑ p : Fin 2, ∑ i : Fin 3,
      (mass (b p) : ℂ)*mass (e i)*
      ((q (φ (ψ t))).delta (b p) (e i)/(q (φ (ψ t))).inverseScale)*
      (q (φ (ψ t))).torqueCorrection (b p) (e i)) = fun _ => 0 from funext he]
    exact tendsto_const_nhds
  have htorque : (∑ p : Fin 2, ∑ i : Fin 3,
      (mass (b p) : ℂ)*mass (e i)*C p i) = 0 := by
    simpa only [mul_neg_one,Finset.sum_neg_distrib,neg_eq_zero] using hz
  exact ⟨⟨r,hr0,U,hU,hpair,C,hCsq,htorque⟩⟩

end CentralConfigurations
