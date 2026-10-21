import CentralConfigurations.FiveBody.D2Actual.PairLimit
import CentralConfigurations.Model.Virial

/-! One actual extraction for D2, retaining its signed metric roots and scalar. -/

namespace CentralConfigurations.FiveBody.D2
open Filter Asymptotics
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

theorem five_potential_split {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) :
    q.toNormalized.potential =
      mass 3 * mass 4 * q.delta 3 4 +
      (mass 0 * mass 1 * q.delta 0 1 + mass 0 * mass 2 * q.delta 0 2 +
        mass 1 * mass 2 * q.delta 1 2) +
      ∑ p : Fin 2, ∑ i : Fin 3,
        mass (Fin.natAdd 3 p) * mass (i.castLE (by decide)) *
          q.delta (Fin.natAdd 3 p) (i.castLE (by decide)) := by
  rw [NormalizedSystem.potential_eq_unordered]
  simp [NormalizedSystem.unorderedPotential, Fin.sum_univ_succ, ZWSystem.toNormalized,
    q.delta_symm 3 0, q.delta_symm 3 1, q.delta_symm 3 2,
    q.delta_symm 4 0, q.delta_symm 4 1, q.delta_symm 4 2]
  ring

theorem three_potential {mass : Fin 3 → ℂ} (r : ZWSystem ℂ 3 mass) :
    r.toNormalized.potential = mass 0 * mass 1 * r.delta 0 1 +
      mass 0 * mass 2 * r.delta 0 2 + mass 1 * mass 2 * r.delta 1 2 := by
  rw [NormalizedSystem.potential_eq_unordered]
  simp [NormalizedSystem.unorderedPotential, Fin.sum_univ_succ, ZWSystem.toNormalized]

/-- Every root and small coordinate is a limit of the same actual sequence.
The arbitrary complex scalar is retained exactly, without a physical-floor premise. -/
structure ActualLimit (m : Fin 5 → ℝ)
    (q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ)))
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (I : ℂ)
    extends FiveBodySource18Certificate m where
  subsequence : ℕ → ℕ
  strictMono : StrictMono subsequence
  triangle_w_eq : ∀ i, triangle.w i = l.w.position (i.castLE (by decide))
  pairZ_eq : ∀ p, pairZ p = l.z.position (Fin.natAdd 3 p)
  pairW : Fin 2 → ℂ
  pairDelta : ℂ
  pair_delta_cube : pairDelta ^ 3 = ((m 3 : ℂ) + m 4)⁻¹
  triangle_z_limit : ∀ i, Tendsto
    (fun t => (q (subsequence t)).z (i.castLE (by decide)) /
      (q (subsequence t)).inverseScale) atTop (𝓝 (triangle.z i))
  triangle_delta_limit : ∀ i j, Tendsto
    (fun t => (q (subsequence t)).delta (i.castLE (by decide))
      (j.castLE (by decide))) atTop (𝓝 (triangle.delta i j))
  pair_w_limit : ∀ p, Tendsto
    (fun t => (q (subsequence t)).w (Fin.natAdd 3 p) /
      (q (subsequence t)).inverseScale) atTop (𝓝 (pairW p))
  pair_delta_limit : Tendsto (fun t => (q (subsequence t)).delta 3 4)
    atTop (𝓝 pairDelta)
  cross_scaled_limit : ∀ (p : Fin 2) (i : Fin 3), Tendsto
    (fun t => (q (subsequence t)).delta (Fin.natAdd 3 p) (i.castLE (by decide)) /
      (q (subsequence t)).inverseScale) atTop (𝓝 (cross p i))
  cross_delta_limit : ∀ (p : Fin 2) (i : Fin 3), Tendsto
    (fun t => (q (subsequence t)).delta (Fin.natAdd 3 p) (i.castLE (by decide)))
      atTop (𝓝 0)
  cross_w_force_limit : ∀ (p : Fin 2) (i : Fin 3), Tendsto
    (fun t => (q (subsequence t)).wForce (Fin.natAdd 3 p) (i.castLE (by decide)) /
      (q (subsequence t)).inverseScale) atTop (𝓝 0)
  scale_limit : Tendsto (fun t => (q (subsequence t)).inverseScale) atTop (𝓝 0)
  exact_scalar : ∀ t, (q (subsequence t)).toNormalized.potential = I
  potential_split : (m 3 : ℂ) * m 4 * pairDelta + triangle.toNormalized.potential = I

theorem exists_actualLimit {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0 < m i) (hd : l.diagramCode = fiveBodySourceDiagram 17)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I : ℂ} (hI : ∀ t, (q t).toNormalized.potential = I) :
    Nonempty (ActualLimit m q l I) := by
  obtain ⟨r, hrw, hr0, φ, hφ, hZ, hD⟩ := l.five_body_source18_triangle_limit hm hd ha
  let e : Fin 3 → Fin 5 := fun i => i.castLE (by decide)
  let b : Fin 2 → Fin 5 := Fin.natAdd 3
  let U : Fin 2 → ℂ := fun p => l.z.position (b p)
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
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
    rw [← hrw i]; exact hr0 i
  have hpair : (m 3 : ℂ) * U 0 + m 4 * U 1 = 0 := by
    simpa [U, b] using l.z_component_balance_of_code hd {3,4} (by decide +kernel)
  have hsq (p : Fin 2) (i : Fin 3) :
      Tendsto (fun t => ((q (φ t)).delta (b p) (e i) /
        (q (φ t)).inverseScale) ^ 2) atTop (𝓝 ((-(U p * r.w i))⁻¹)) := by
    have h := l.delta_div_scale_squared_limit hs (b p) (e i)
      (by rw [hZe i]; exact hU p) (by rw [hWb p]; exact (hWe i).symm)
    simpa only [hZe i, hWb p, sub_zero, zero_sub, mul_neg, hrw i]
      using h.comp hφ.tendsto_atTop
  have hsmall (p : Fin 2) : (fun t => (q t).w (b p)) =O[atTop]
      (fun t => (q t).inverseScale) := by
    have h := l.five_body_source18_small_positions hm hd
    fin_cases p
    · exact h.2.1
    · exact h.2.2
  let f : ℕ → (Unit ⊕ (Fin 2 ⊕ (Fin 2 × Fin 3))) → ℂ := fun t c => match c with
    | .inl _ => (q (φ t)).delta 3 4
    | .inr (.inl p) => (q (φ t)).w (b p) / (q (φ t)).inverseScale
    | .inr (.inr (p,i)) => (q (φ t)).delta (b p) (e i) / (q (φ t)).inverseScale
  have hb : ∀ c, Bornology.IsBounded (Set.range (fun t => f t c)) := by
    intro c
    rcases c with u | p | ⟨p,i⟩
    · exact bounded_of_power_tendsto (by decide : (3 : ℕ) ≠ 0)
        ((pair_delta_cube_limit l hd hm).comp hφ.tendsto_atTop)
    · apply (bounded_range_div_of_bigO (hsmall p)).subset
      rintro _ ⟨t, rfl⟩
      exact ⟨φ t, rfl⟩
    · exact bounded_of_power_tendsto (by decide : (2 : ℕ) ≠ 0) (hsq p i)
  obtain ⟨v, ψ, hψ, hv⟩ := exists_finite_coordinate_limits f hb
  let Φ : ℕ → ℕ := fun t => φ (ψ t)
  have hΦ : StrictMono Φ := hφ.comp hψ
  let D : ℂ := v (.inl ())
  let V : Fin 2 → ℂ := fun p => v (.inr (.inl p))
  let C : Fin 2 → Fin 3 → ℂ := fun p i => v (.inr (.inr (p,i)))
  have hδ : Tendsto (fun t => (q (Φ t)).delta 3 4) atTop (𝓝 D) := hv (.inl ())
  have hV (p : Fin 2) : Tendsto
      (fun t => (q (Φ t)).w (b p) / (q (Φ t)).inverseScale) atTop (𝓝 (V p)) :=
    hv (.inr (.inl p))
  have hC (p : Fin 2) (i : Fin 3) : Tendsto
      (fun t => (q (Φ t)).delta (b p) (e i) / (q (Φ t)).inverseScale)
        atTop (𝓝 (C p i)) := hv (.inr (.inr (p,i)))
  have hδcube : D ^ 3 = ((m 3 : ℂ) + m 4)⁻¹ :=
    tendsto_nhds_unique (hδ.pow 3) ((pair_delta_cube_limit l hd hm).comp hΦ.tendsto_atTop)
  have hCsq (p : Fin 2) (i : Fin 3) : C p i ^ 2 * (-(U p * r.w i)) = 1 := by
    have h := tendsto_nhds_unique ((hC p i).pow 2) ((hsq p i).comp hψ.tendsto_atTop)
    rw [h, inv_mul_cancel₀ (neg_ne_zero.mpr (mul_ne_zero (hU p) (hr0 i)))]
  have hT (p : Fin 2) (i : Fin 3) : Tendsto
      (fun t => (q (Φ t)).torqueCorrection (b p) (e i)) atTop (𝓝 (-1)) := by
    have hbi : b p ≠ e i := by fin_cases p <;> fin_cases i <;> decide +kernel
    exact (l.opposite_position_torque_limit (b p) (e i) hbi (hU p)
      (hZe i) (hWb p) (hWe i)).comp hΦ.tendsto_atTop
  have hsum := tendsto_finsetSum Finset.univ (fun p _ =>
    tendsto_finsetSum Finset.univ (fun i _ =>
      ((hC p i).const_mul ((m (b p) : ℂ) * m (e i))).mul (hT p i)))
  have he (t : ℕ) := (q (Φ t)).five_body_pair_triangle_normalized_torque_zero
    (q (Φ t)).inverseScale
  have hz : (∑ p : Fin 2, ∑ i : Fin 3,
      (m (b p) : ℂ) * m (e i) * C p i * (-1)) = 0 := by
    apply tendsto_nhds_unique hsum
    simp only [show (fun t => ∑ p : Fin 2, ∑ i : Fin 3,
      (m (b p) : ℂ) * m (e i) *
      ((q (Φ t)).delta (b p) (e i) / (q (Φ t)).inverseScale) *
      (q (Φ t)).torqueCorrection (b p) (e i)) = fun _ => 0 from funext he]
    exact tendsto_const_nhds
  have htorque : (∑ p : Fin 2, ∑ i : Fin 3,
      (m (b p) : ℂ) * m (e i) * C p i) = 0 := by
    simpa only [mul_neg_one, Finset.sum_neg_distrib, neg_eq_zero] using hz
  have hcross (p : Fin 2) (i : Fin 3) : Tendsto
      (fun t => (q (Φ t)).delta (b p) (e i)) atTop (𝓝 0) :=
    (cross_delta_zero l hd p i).comp hΦ.tendsto_atTop
  have htr : Tendsto
      (fun t => (m 0 : ℂ) * m 1 * (q (Φ t)).delta 0 1 +
        (m 0 : ℂ) * m 2 * (q (Φ t)).delta 0 2 +
        (m 1 : ℂ) * m 2 * (q (Φ t)).delta 1 2)
      atTop (𝓝 r.toNormalized.potential) := by
    rw [three_potential]
    exact (((hD 0 1).comp hψ.tendsto_atTop).const_mul _).add
      (((hD 0 2).comp hψ.tendsto_atTop).const_mul _) |>.add
        (((hD 1 2).comp hψ.tendsto_atTop).const_mul _)
  have hcrossSum := tendsto_finsetSum Finset.univ (fun p _ =>
    tendsto_finsetSum Finset.univ (fun i _ =>
      (hcross p i).const_mul ((m (b p) : ℂ) * m (e i))))
  simp only [mul_zero, Finset.sum_const_zero] at hcrossSum
  have htotal := (((hδ.const_mul ((m 3 : ℂ) * m 4)).add htr).add hcrossSum)
  simp only [add_zero] at htotal
  have hsplit : (m 3 : ℂ) * m 4 * D + r.toNormalized.potential = I := by
    apply tendsto_nhds_unique htotal
    have heq t : (m 3 : ℂ) * m 4 * (q (Φ t)).delta 3 4 +
        ((m 0 : ℂ) * m 1 * (q (Φ t)).delta 0 1 +
          (m 0 : ℂ) * m 2 * (q (Φ t)).delta 0 2 +
          (m 1 : ℂ) * m 2 * (q (Φ t)).delta 1 2) +
        ∑ p : Fin 2, ∑ i : Fin 3, (m (b p) : ℂ) * m (e i) *
          (q (Φ t)).delta (b p) (e i) = I := by
      exact (five_potential_split (q (Φ t))).symm.trans (hI (Φ t))
    simp only [show (fun t => (m 3 : ℂ) * m 4 * (q (Φ t)).delta 3 4 +
        ((m 0 : ℂ) * m 1 * (q (Φ t)).delta 0 1 +
          (m 0 : ℂ) * m 2 * (q (Φ t)).delta 0 2 +
          (m 1 : ℂ) * m 2 * (q (Φ t)).delta 1 2) +
        ∑ p : Fin 2, ∑ i : Fin 3, (m (b p) : ℂ) * m (e i) *
          (q (Φ t)).delta (b p) (e i)) = fun _ => I from funext heq]
    exact tendsto_const_nhds
  exact ⟨{
    triangle := r, w_ne_zero := hr0, pairZ := U, pairZ_ne_zero := hU,
    pair_balance := hpair, cross := C, cross_square := hCsq, cross_torque := htorque,
    subsequence := Φ, strictMono := hΦ, triangle_w_eq := hrw, pairZ_eq := fun _ => rfl,
    pairW := V, pairDelta := D, pair_delta_cube := hδcube,
    triangle_z_limit := fun i => (hZ i).comp hψ.tendsto_atTop,
    triangle_delta_limit := fun i j => (hD i j).comp hψ.tendsto_atTop,
    pair_w_limit := hV, pair_delta_limit := hδ, cross_scaled_limit := hC,
    cross_delta_limit := hcross,
    cross_w_force_limit := fun p i =>
      (cross_wForce_div_scale_zero l hd ha p i).comp hΦ.tendsto_atTop,
    scale_limit := ha.comp hΦ.tendsto_atTop,
    exact_scalar := fun t => hI (Φ t), potential_split := hsplit }⟩

end CentralConfigurations.FiveBody.D2
