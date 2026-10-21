import CentralConfigurations.Asymptotics.FourthPowerExtraction
import Mathlib.Topology.Bornology.Constructions

/-! Finite simultaneous extraction for bounded complex coordinates. -/

namespace CentralConfigurations
open Filter Asymptotics
open scoped Topology

theorem bounded_range_div_of_bigO {f g : ℕ → ℂ} (h : f =O[atTop] g) :
    Bornology.IsBounded (Set.range (fun t => f t / g t)) := by
  obtain ⟨C,hC⟩ := (div_isBoundedUnder_of_isBigO h).bddAbove_range
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨C, ?_⟩
  rintro _ ⟨t,rfl⟩
  exact hC ⟨t,rfl⟩

theorem bounded_range_of_bigO_one {f : ℕ → ℂ}
    (h : f =O[atTop] (fun _ => (1 : ℂ))) :
    Bornology.IsBounded (Set.range f) := by
  simpa only [div_one] using bounded_range_div_of_bigO h

theorem bounded_of_power_tendsto {f : ℕ → ℂ} {v : ℂ} {k : ℕ}
    (hk : k ≠ 0) (h : Tendsto (fun t => f t ^ k) atTop (𝓝 v)) :
    Bornology.IsBounded (Set.range f) := by
  apply bounded_range_of_bigO_one
  apply IsBigO.of_pow hk
  change (fun t => f t ^ k) =O[atTop] (fun _ => (1 : ℂ) ^ k)
  simpa only [one_pow] using h.isBigO_one ℂ

theorem exists_finite_coordinate_limits {ι : Type*} [Fintype ι]
    (f : ℕ → ι → ℂ)
    (hb : ∀ i, Bornology.IsBounded (Set.range (fun t => f t i))) :
    ∃ v : ι → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ i, Tendsto (fun t => f (φ t) i) atTop (𝓝 (v i)) := by
  have hB := Bornology.IsBounded.pi hb
  obtain ⟨v,_,φ,hφ,hlim⟩ := tendsto_subseq_of_bounded hB
    (fun t => show f t ∈ Set.pi Set.univ (fun i => Set.range (fun s => f s i)) from
      fun i _ => ⟨t,rfl⟩)
  refine ⟨v,φ,hφ,fun i => ?_⟩
  exact ((continuous_apply i).tendsto v).comp hlim

end CentralConfigurations
