import CentralConfigurations.Asymptotics.FourthPowerExtraction

/-! Common compact extraction retaining three independent square-root branches. -/

namespace CentralConfigurations
open Filter
open scoped Topology

theorem bounded_of_square_tendsto {f : ℕ → ℂ} {u : ℂ}
    (hf : Tendsto (fun t => f t ^ 2) atTop (𝓝 u)) :
    Bornology.IsBounded (Set.range f) := by
  apply bounded_of_fourth_power_tendsto (v := u^2)
  simpa only [← pow_mul] using hf.pow 2

theorem exists_simultaneous_three_square_limits {f g h : ℕ → ℂ} {u v w : ℂ}
    (hf : Tendsto (fun t => f t ^ 2) atTop (𝓝 u))
    (hg : Tendsto (fun t => g t ^ 2) atTop (𝓝 v))
    (hh : Tendsto (fun t => h t ^ 2) atTop (𝓝 w)) :
    ∃ x y z : ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (f ∘ φ) atTop (𝓝 x) ∧ Tendsto (g ∘ φ) atTop (𝓝 y) ∧
      Tendsto (h ∘ φ) atTop (𝓝 z) ∧ x^2 = u ∧ y^2 = v ∧ z^2 = w := by
  have hb := (bounded_of_square_tendsto hf).prod
    ((bounded_of_square_tendsto hg).prod (bounded_of_square_tendsto hh))
  obtain ⟨⟨x,y,z⟩, _, φ, hφ, hlim⟩ := tendsto_subseq_of_bounded hb
    (fun t => show (f t, g t, h t) ∈ Set.range f ×ˢ (Set.range g ×ˢ Set.range h)
      from ⟨⟨t,rfl⟩,⟨t,rfl⟩,⟨t,rfl⟩⟩)
  have hx : Tendsto (f ∘ φ) atTop (𝓝 x) := (continuous_fst.tendsto _).comp hlim
  have hy : Tendsto (g ∘ φ) atTop (𝓝 y) :=
    (continuous_fst.tendsto _).comp ((continuous_snd.tendsto _).comp hlim)
  have hz : Tendsto (h ∘ φ) atTop (𝓝 z) :=
    (continuous_snd.tendsto _).comp ((continuous_snd.tendsto _).comp hlim)
  exact ⟨x,y,z,φ,hφ,hx,hy,hz,
    tendsto_nhds_unique (hx.pow 2) (hf.comp hφ.tendsto_atTop),
    tendsto_nhds_unique (hy.pow 2) (hg.comp hφ.tendsto_atTop),
    tendsto_nhds_unique (hz.pow 2) (hh.comp hφ.tendsto_atTop)⟩

end CentralConfigurations
