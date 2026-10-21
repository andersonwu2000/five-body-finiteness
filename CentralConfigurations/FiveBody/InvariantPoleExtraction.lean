import CentralConfigurations.FiveBody.FixedLevelFiniteness

/-!
# Potential and original four-products survive balanced extraction

The extraction returns actual balanced solutions, one common subsequence,
the exact numerical potential, and the original selected pole. It does not
preserve membership of the rotation slice after balancing.
-/

namespace CentralConfigurations
noncomputable section
open scoped Topology BigOperators
open Filter

theorem ZWSystem.rescale_squaredSeparation {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (a : ℂ) (ha : a ≠ 0) (i j : Fin n) :
    squaredSeparation (q.rescale a ha).toNormalized.x
      (q.rescale a ha).toNormalized.y i j =
      squaredSeparation q.toNormalized.x q.toNormalized.y i j := by
  simp only [squaredSeparation, ZWSystem.toNormalized]
  rw [inverse_zw_separation, inverse_zw_separation]
  change (a * q.z i - a * q.z j) * (a⁻¹ * q.w i - a⁻¹ * q.w j) = _
  calc
    _ = (a * a⁻¹) * ((q.z i - q.z j) * (q.w i - q.w j)) := by ring
    _ = _ := by rw [mul_inv_cancel₀ ha, one_mul]

theorem ZWSystem.swap_squaredSeparation {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) :
    squaredSeparation q.swap.toNormalized.x q.swap.toNormalized.y i j =
      squaredSeparation q.toNormalized.x q.toNormalized.y i j := by
  simp only [squaredSeparation, ZWSystem.toNormalized]
  rw [inverse_zw_separation, inverse_zw_separation]
  exact mul_comm _ _

theorem ZWSystem.rescale_fourProduct {mass : Fin 5 → ℂ}
    (q : ZWSystem ℂ 5 mass) (a : ℂ) (ha : a ≠ 0) (e : Fin 10) :
    (q.rescale a ha).toNormalized.fiveBodyFourProduct e =
      q.toNormalized.fiveBodyFourProduct e := by
  unfold NormalizedSystem.fiveBodyFourProduct
  congr 1
  funext k
  exact q.rescale_squaredSeparation a ha _ _

theorem ZWSystem.swap_fourProduct {mass : Fin 5 → ℂ}
    (q : ZWSystem ℂ 5 mass) (e : Fin 10) :
    q.swap.toNormalized.fiveBodyFourProduct e = q.toNormalized.fiveBodyFourProduct e := by
  unfold NormalizedSystem.fiveBodyFourProduct
  congr 1
  funext k
  exact q.swap_squaredSeparation _ _

theorem ZWSystem.balanced_fourProduct {mass : Fin 5 → ℂ}
    (q : ZWSystem ℂ 5 mass) (i j : Fin 5) (hij : i ≠ j) (e : Fin 10) :
    (q.balanced i j hij).toNormalized.fiveBodyFourProduct e =
      q.toNormalized.fiveBodyFourProduct e :=
  q.rescale_fourProduct _ _ e

theorem NormalizedSystem.toZW_fourProduct {mass : Fin 5 → ℂ}
    (q : NormalizedSystem ℂ 5 mass) (e : Fin 10) :
    q.toZW.toNormalized.fiveBodyFourProduct e = q.fiveBodyFourProduct e := by
  unfold NormalizedSystem.fiveBodyFourProduct
  congr 1
  funext k
  unfold fiveBodyDistanceData squaredSeparation
  simp only [NormalizedSystem.toZW_toNormalized_x, NormalizedSystem.toZW_toNormalized_y]

theorem NormalizedSystem.toZW_unorderedPotential {n : ℕ} {mass : Fin n → ℂ}
    (q : NormalizedSystem ℂ n mass) :
    q.toZW.toNormalized.unorderedPotential = q.unorderedPotential := rfl

theorem ZWSystem.balanced_selectedProduct {mass : Fin 5 → ℂ}
    (q : ZWSystem ℂ 5 mass) (i j : Fin 5) (hij : i ≠ j) (R : Finset (Fin 10)) :
    (q.balanced i j hij).toNormalized.fiveBodySelectedProduct R =
      q.toNormalized.fiveBodySelectedProduct R := by
  simp only [NormalizedSystem.fiveBodySelectedProduct, ZWSystem.balanced_fourProduct]

theorem four_product_pole_source_unbounded {mass : Fin 5 → ℂ}
    (q : ℕ → NormalizedSystem ℂ 5 mass) (e : Fin 10)
    (hpole : Tendsto (fun t => ‖(q t).fiveBodyFourProduct e‖) atTop atTop) :
    ¬ BddAbove (Set.range
      (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖)) := by
  rintro ⟨B, hB⟩
  have hbound (t : ℕ) : ‖(q t).fiveBodyFourProduct e‖ ≤ (4 * (max B 0) ^ 2) ^ 4 :=
    (q t).four_product_norm_le_source_bound (le_max_right B 0)
      ((hB (Set.mem_range_self t)).trans (le_max_left B 0)) e
  obtain ⟨t, ht⟩ :=
    (hpole.eventually (eventually_gt_atTop ((4 * (max B 0) ^ 2) ^ 4))).exists
  exact not_lt_of_ge (hbound t) ht

theorem exists_invariant_singular_limit_of_four_product_pole {mass : Fin 5 → ℂ}
    (q : ℕ → NormalizedSystem ℂ 5 mass) (i j : Fin 5) (hij : i ≠ j)
    (c : ℂ) (hq : ∀ t, q t ∈ fixedPotentialGauge mass i j c) (e : Fin 10)
    (hpole : Tendsto (fun t => ‖(q t).fiveBodyFourProduct e‖) atTop atTop) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
        atTop (𝓝 0) ∧
      (∀ t, ((q (l.subsequence t)).toZW.balanced i j hij).toNormalized.potential = c) ∧
      Tendsto (fun t => ‖((q (l.subsequence t)).toZW.balanced i j hij).toNormalized.fiveBodyFourProduct e‖)
        atTop atTop := by
  obtain ⟨l, hl⟩ := exists_gauged_singular_limit_of_unbounded q i j hij
    (fun t => (hq t).1) (four_product_pole_source_unbounded q e hpole)
  refine ⟨l, hl, ?_, ?_⟩
  · intro t
    rw [NormalizedSystem.potential_eq_unordered, ZWSystem.balanced_unorderedPotential,
      NormalizedSystem.toZW_unorderedPotential]
    exact (hq (l.subsequence t)).2
  · simpa only [ZWSystem.balanced_fourProduct, NormalizedSystem.toZW_fourProduct,
      Function.comp_def] using
      hpole.comp l.strictMono.tendsto_atTop

end
end CentralConfigurations
