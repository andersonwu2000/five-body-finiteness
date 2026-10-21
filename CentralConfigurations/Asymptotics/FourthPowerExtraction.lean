import CentralConfigurations.Asymptotics.Extraction
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Tactic

/-!
# Compact extraction for inverse-distance fourth powers

A convergent fourth power bounds every branch of the original complex sequence.
No principal root is selected. Two such sequences have one common subsequence.
-/

namespace CentralConfigurations

open Filter
open scoped Topology

theorem norm_le_one_add_fourth (z : ℂ) : ‖z‖ ≤ 1 + ‖z ^ 4‖ := by
  rw [norm_pow]
  have hn := norm_nonneg z
  nlinarith [sq_nonneg (‖z‖ ^ 2 - 1), sq_nonneg (‖z‖ - 1)]

theorem bounded_of_fourth_power_tendsto {f : ℕ → ℂ} {v : ℂ}
    (h : Tendsto (fun t => f t ^ 4) atTop (𝓝 v)) :
    Bornology.IsBounded (Set.range f) := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_range_of_tendsto _ h).exists_norm_le
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1 + C, ?_⟩
  rintro _ ⟨t, rfl⟩
  have hbound := hC _ ⟨t, rfl⟩
  have hnorm := norm_le_one_add_fourth (f t)
  linarith

theorem exists_simultaneous_fourth_power_limits {f g : ℕ → ℂ} {u v : ℂ}
    (hf : Tendsto (fun t => f t ^ 4) atTop (𝓝 u))
    (hg : Tendsto (fun t => g t ^ 4) atTop (𝓝 v)) :
    ∃ x y : ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (f ∘ φ) atTop (𝓝 x) ∧ Tendsto (g ∘ φ) atTop (𝓝 y) ∧
      x ^ 4 = u ∧ y ^ 4 = v := by
  have hb := (bounded_of_fourth_power_tendsto hf).prod (bounded_of_fourth_power_tendsto hg)
  obtain ⟨⟨x, y⟩, _, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hb
    (fun t => show (f t, g t) ∈ Set.range f ×ˢ Set.range g from ⟨⟨t, rfl⟩, ⟨t, rfl⟩⟩)
  have hx : Tendsto (f ∘ φ) atTop (𝓝 x) := (continuous_fst.tendsto (x, y)).comp hlim
  have hy : Tendsto (g ∘ φ) atTop (𝓝 y) := (continuous_snd.tendsto (x, y)).comp hlim
  exact ⟨x, y, φ, hφ, hx, hy,
    tendsto_nhds_unique (hx.pow 4) (hf.comp hφ.tendsto_atTop),
    tendsto_nhds_unique (hy.pow 4) (hg.comp hφ.tendsto_atTop)⟩

end CentralConfigurations
