import CentralConfigurations.Asymptotics.FourthPowerExtraction
import CentralConfigurations.Asymptotics.PairEstimates

/-!
# Common nonzero limits of comparable complex ratios

Secondary force normalization in Sections 10.2 and 11.8. Compactness is
applied to actual complex ratios, retaining every phase and branch.
-/

namespace CentralConfigurations

open Filter Asymptotics
open scoped Topology

theorem nonzero_ratio_limit_of_theta {f b : ℕ → ℂ} {u : ℂ}
    (hb : ∀ t, b t ≠ 0) (ht : f =Θ[atTop] b)
    (hu : Tendsto (fun t => f t / b t) atTop (𝓝 u)) : u ≠ 0 := by
  intro hz
  rw [hz] at hu
  have hs : f =o[atTop] b := (isLittleO_iff_tendsto'
    (Eventually.of_forall fun t h => (hb t h).elim)).mpr hu
  exact isLittleO_irrefl (Eventually.of_forall hb).frequently (ht.2.trans_isLittleO hs)

theorem exists_two_nonzero_ratio_limits {f g b : ℕ → ℂ}
    (hb : ∀ t, b t ≠ 0) (hf : f =Θ[atTop] b) (hg : g =Θ[atTop] b) :
    ∃ U V : ℂ, U ≠ 0 ∧ V ≠ 0 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun t => f (φ t) / b (φ t)) atTop (𝓝 U) ∧
      Tendsto (fun t => g (φ t) / b (φ t)) atTop (𝓝 V) := by
  obtain ⟨C, _, hC⟩ := hf.1.exists_pos
  obtain ⟨D, _, hD⟩ := hg.1.exists_pos
  have hmem : ∀ᶠ t in atTop, (f t / b t, g t / b t) ∈
      Metric.closedBall (0 : ℂ) C ×ˢ Metric.closedBall (0 : ℂ) D := by
    filter_upwards [hC.bound, hD.bound] with t ht hs
    constructor
    · simp only [Metric.mem_closedBall, dist_zero_right, norm_div]
      exact (div_le_iff₀ (norm_pos_iff.mpr (hb t))).mpr ht
    · simp only [Metric.mem_closedBall, dist_zero_right, norm_div]
      exact (div_le_iff₀ (norm_pos_iff.mpr (hb t))).mpr hs
  obtain ⟨⟨U, V⟩, _, φ, hφ, hv⟩ :=
    ((isCompact_closedBall (0 : ℂ) C).prod (isCompact_closedBall (0 : ℂ) D)).tendsto_subseq'
      hmem.frequently
  have hU : Tendsto (fun t => f (φ t) / b (φ t)) atTop (𝓝 U) :=
    (continuous_fst.tendsto (U, V)).comp hv
  have hV : Tendsto (fun t => g (φ t) / b (φ t)) atTop (𝓝 V) :=
    (continuous_snd.tendsto (U, V)).comp hv
  exact ⟨U, V, nonzero_ratio_limit_of_theta (fun t => hb (φ t))
    ⟨hf.1.comp_tendsto hφ.tendsto_atTop, hf.2.comp_tendsto hφ.tendsto_atTop⟩ hU,
    nonzero_ratio_limit_of_theta (fun t => hb (φ t))
      ⟨hg.1.comp_tendsto hφ.tendsto_atTop, hg.2.comp_tendsto hφ.tendsto_atTop⟩ hV, φ, hφ, hU, hV⟩

end CentralConfigurations
