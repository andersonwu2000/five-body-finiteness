import CentralConfigurations.FiveBody.D8.Exclusion
import CentralConfigurations.FiveBody.D6Butterfly.Exclusion
import CentralConfigurations.FiveBody.RemainingAnalyticCases
import CentralConfigurations.FiveBody.OrdinaryCanonicalBranches
import CentralConfigurations.FiveBody.PairEnergyExclusion
import CentralConfigurations.FiveBody.D3CycleEnergy
import CentralConfigurations.FiveBody.D5RProduct
import CentralConfigurations.FiveBody.D9RawExclusion

/-!
# Local conclusions for the sixteen source cases

The case analysis takes the D2 exclusion as an explicit parameter and
combines it with the other local exclusions, four-product bounds, and D5
decay. D2Regular/PositiveFiniteness.lean supplies that parameter for positive
masses in every common labeling.
-/

namespace CentralConfigurations.FiveBody.Classification
noncomputable section
open Filter
open scoped Topology

theorem completeRProduct_zero_of_surviving_source
    {m : Fin 5 → ℝ} (hm : ∀ i, 0 < m i)
    (hremaining : RemainingAnalyticCases m) (σ : Equiv.Perm (Fin 5))
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m (σ i) : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero)
    {k : Fin 20} (hd : l.diagramCode = fiveBodySourceDiagram k)
    (hk : k ∈ fiveBodyOrderSurvivors)
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel (m ∘ σ) I0)
    (hI : ∀ t, (q t).toNormalized.potential = (I0 : ℂ))
    (he : FourProductEscapes q) :
    Tendsto (fun t => (q t).toNormalized.fiveBodySelectedProduct (RZero.completeR (m ∘ σ)))
      atTop (𝓝 0) := by
  have hmr : ∀ i, 0 < (m ∘ σ) i := fun i => hm (σ i)
  have hIu : ∀ t, (q t).toNormalized.unorderedPotential = (I0 : ℂ) :=
    fun t => (q t).toNormalized.potential_eq_unordered.symm.trans (hI t)
  have hmem : k ∈ Finset.univ.image Ordinary.changIndex := by
    rw [Ordinary.chang_indices_exact_survivors]
    exact hk
  obtain ⟨d, _, hdk⟩ := Finset.mem_image.mp hmem
  subst k
  fin_cases d
  · exact (PairEnergy.false_of_chang5 l hmr hb hd ha hphysical hI).elim
  · exact ((hremaining.d2 σ) q l hmr hb hd ha I0 hphysical hI).elim
  · exact (D3.false_of_chang20 l hmr hd ha hb hphysical hI).elim
  · exact (PairEnergy.false_of_chang6 l hmr hb hd ha hphysical hI).elim
  · exact D5.completeRProduct_tendsto_zero_of_chang3 l hmr hb hd ha hphysical hI
  · exact (D6.false_of_chang19 l hmr hd hb ha).elim
  · exact (Ordinary.not_escaping_of_chang4_physical_potential l hmr hb hd ha hphysical hIu he).elim
  · exact (D8.false_of_chang7 l hmr hd hb ha hphysical hI).elim
  · exact (D9Raw.false_of_chang12_physical_potential l hmr hb hd ha hphysical hI).elim
  · exact (Ordinary.not_escaping_of_chang_d10_d16 l
      (complex_positive_masses_admissible (m ∘ σ) hmr) hb ha hz hw (d := 9) hd (by decide) he).elim
  · exact (Ordinary.not_escaping_of_chang_d10_d16 l
      (complex_positive_masses_admissible (m ∘ σ) hmr) hb ha hz hw (d := 10) hd (by decide) he).elim
  · exact (Ordinary.not_escaping_of_chang_d10_d16 l
      (complex_positive_masses_admissible (m ∘ σ) hmr) hb ha hz hw (d := 11) hd (by decide) he).elim
  · exact (Ordinary.not_escaping_of_chang_d10_d16 l
      (complex_positive_masses_admissible (m ∘ σ) hmr) hb ha hz hw (d := 12) hd (by decide) he).elim
  · exact (Ordinary.not_escaping_of_chang_d10_d16 l
      (complex_positive_masses_admissible (m ∘ σ) hmr) hb ha hz hw (d := 13) hd (by decide) he).elim
  · exact (Ordinary.not_escaping_of_chang_d10_d16 l
      (complex_positive_masses_admissible (m ∘ σ) hmr) hb ha hz hw (d := 14) hd (by decide) he).elim
  · exact (Ordinary.not_escaping_of_chang_d10_d16 l
      (complex_positive_masses_admissible (m ∘ σ) hmr) hb ha hz hw (d := 15) hd (by decide) he).elim

end
end CentralConfigurations.FiveBody.Classification
