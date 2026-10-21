import CentralConfigurations.Model.PotentialFiniteness
import CentralConfigurations.Model.ZW
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Uniform potential bounds from Lemma 2.2

The bound depends only on the fixed masses. Thus it holds on every
sequence of normalized solutions, before or after extraction, balancing,
or relabeling. No compactness of the configuration space is assumed.
-/

namespace CentralConfigurations

open Filter Asymptotics

theorem NormalizedSystem.potential_norm_bounded {n : ℕ} (mass : Fin n → ℂ) :
    ∃ C : ℝ, ∀ q : NormalizedSystem ℂ n mass, ‖q.unorderedPotential‖ ≤ C := by
  obtain ⟨C, hC⟩ := (finite_potential_values mass).isBounded.exists_norm_le
  exact ⟨C, fun q => hC q.unorderedPotential ⟨q, rfl⟩⟩

theorem NormalizedSystem.unorderedPotential_isBigO_one {α : Type*} {n : ℕ}
    {mass : Fin n → ℂ} (q : α → NormalizedSystem ℂ n mass) (l : Filter α) :
    (fun t => (q t).unorderedPotential) =O[l] (fun _ => (1 : ℂ)) := by
  obtain ⟨C, hC⟩ := potential_norm_bounded mass
  apply isBigO_iff.mpr
  refine ⟨C, Filter.Eventually.of_forall fun t => ?_⟩
  simpa only [norm_one, mul_one] using hC (q t)

theorem ZWSystem.unorderedPotential_isBigO_one {α : Type*} {n : ℕ}
    {mass : Fin n → ℂ} (q : α → ZWSystem ℂ n mass) (l : Filter α) :
    (fun t => (q t).toNormalized.unorderedPotential) =O[l] (fun _ => (1 : ℂ)) :=
  NormalizedSystem.unorderedPotential_isBigO_one (fun t => (q t).toNormalized) l

end CentralConfigurations
