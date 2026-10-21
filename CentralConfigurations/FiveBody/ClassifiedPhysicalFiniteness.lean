import CentralConfigurations.FiveBody.ActualClassification
import CentralConfigurations.FiveBody.FixedLevelPhysicalFiniteness

/-!
# Physical finiteness from the classified local cases

Both polynomial selections use the same physical potential value and the
same complete mass-indexed R product. The classified cases imply the local
decay statement, conditional on the D2 exclusion supplied by
D2Regular/PositiveFiniteness.lean.
-/

namespace CentralConfigurations.FiveBody.Classification
noncomputable section
open Filter
open scoped Topology BigOperators

theorem fixed_level_decay_of_remaining_cases (m : Fin 5 → ℝ)
    (hm : ∀ i, 0 < m i) (hremaining : RemainingAnalyticCases m)
    (i j : Fin 5) (hij : i ≠ j)
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0) :
    FixedLevelFourProductDecay (fun i => (m i : ℂ)) i j (I0 : ℂ) (RZero.completeR m) := by
  intro q hq e hpole
  obtain ⟨L,ha,hI,hpole'⟩ := exists_invariant_singular_limit_of_four_product_pole
    q i j hij (I0 : ℂ) hq e hpole
  let qb := fun t => (q (L.subsequence t)).toZW.balanced i j hij
  have hb : ∀ t, ‖(qb t).zVector‖ = ‖(qb t).wVector‖ :=
    fun t => (q (L.subsequence t)).toZW.balanced_norms i j hij
  have he : FourProductEscapes qb := by
    refine ⟨e,?_⟩
    apply hpole'.congr
    intro t
    have h := (qb t).toNormalized.five_body_four_product_toZW e
    exact congrArg norm h.symm
  have hzero := completeRProduct_zero_of_balanced_pole hm hremaining
    L.leading hb ha L.z_nonzero L.w_nonzero hphysical hI he
  refine ⟨L.subsequence,L.strictMono,?_⟩
  apply hzero.congr
  intro t
  dsimp only [qb]
  rw [ZWSystem.balanced_selectedProduct]
  simp only [NormalizedSystem.fiveBodySelectedProduct,NormalizedSystem.toZW_fourProduct]

theorem finite_physical_level_gauge_of_remaining_cases (m : Fin 5 → ℝ)
    (hm : ∀ i, 0 < m i) (hremaining : RemainingAnalyticCases m)
    (i j : Fin 5) (hij : i ≠ j)
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0) :
    (fixedPotentialGauge (fun i => (m i : ℂ)) i j (I0 : ℂ)).Finite :=
  finite_fixedPotentialGauge_of_four_product_decay _ i j hij _ (RZero.completeR m)
    (fixed_level_decay_of_remaining_cases m hm hremaining i j hij hphysical)

/-- Conditional on precisely D2 in every common source labeling.
No complete decay, generic-mass guard, or global finiteness premise remains. -/
theorem finite_physical_classes_of_remaining_cases (m : Fin 5 → ℝ)
    (hm : ∀ i, 0 < m i) (hremaining : RemainingAnalyticCases m)
    (i j : Fin 5) (hij : i ≠ j) :
    Finite (PhysicalSimilarityClass 5 m) :=
  finite_physical_classes_of_fixed_level_decay m hm i j hij (RZero.completeR m)
    (fun _ hc => fixed_level_decay_of_remaining_cases m hm hremaining i j hij hc)

end
end CentralConfigurations.FiveBody.Classification
