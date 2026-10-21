import CentralConfigurations.Asymptotics.OrderLevels
import CentralConfigurations.Asymptotics.PairEstimates

/-!
# The two threshold systems in Section 4.1

Position/separation levels use epsilon^2, epsilon, epsilon^(-2).
Distance levels use epsilon, 1, epsilon^(-2), with level 0 excluded by
Estimate 1. Powers are algebraic; no independent complex root is chosen.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

theorem epsilon_sq_littleO_epsilon (eps : ℕ → ℂ) (hn : ∀ t, eps t ≠ 0)
    (hz : Tendsto eps atTop (𝓝 0)) : (fun t => eps t ^ 2) =o[atTop] eps := by
  apply (isLittleO_iff_tendsto (fun t ht => (hn t ht).elim)).mpr
  convert hz using 1
  funext t
  field_simp [hn t]

theorem epsilon_littleO_inverse_sq (eps : ℕ → ℂ) (hn : ∀ t, eps t ≠ 0)
    (hz : Tendsto eps atTop (𝓝 0)) : eps =o[atTop] (fun t => (eps t)⁻¹ ^ 2) := by
  apply (isLittleO_iff_tendsto (fun t ht =>
    (pow_ne_zero 2 (inv_ne_zero (hn t)) ht).elim)).mpr
  have hp : Tendsto (fun t => eps t ^ 3) atTop (𝓝 0) := by simpa using hz.pow 3
  convert hp using 1
  funext t
  field_simp [hn t]

noncomputable def epsilonPositionScales (eps : ℕ → ℂ) (hn : ∀ t, eps t ≠ 0)
    (hz : Tendsto eps atTop (𝓝 0)) : OrderScales where
  lower t := eps t ^ 2
  middle := eps
  upper t := (eps t)⁻¹ ^ 2
  lower_nonzero := Eventually.of_forall (fun t => pow_ne_zero 2 (hn t))
  middle_nonzero := Eventually.of_forall hn
  upper_nonzero := Eventually.of_forall (fun t => pow_ne_zero 2 (inv_ne_zero (hn t)))
  lower_middle := epsilon_sq_littleO_epsilon eps hn hz
  middle_upper := epsilon_littleO_inverse_sq eps hn hz

noncomputable def epsilonDistanceScales (eps : ℕ → ℂ) (hn : ∀ t, eps t ≠ 0)
    (hz : Tendsto eps atTop (𝓝 0)) : OrderScales where
  lower := eps
  middle := fun _ => 1
  upper t := (eps t)⁻¹ ^ 2
  lower_nonzero := Eventually.of_forall hn
  middle_nonzero := Eventually.of_forall (fun _ => one_ne_zero)
  upper_nonzero := Eventually.of_forall (fun t => pow_ne_zero 2 (inv_ne_zero (hn t)))
  lower_middle := (isLittleO_one_iff ℂ).mpr hz
  middle_upper := by
    apply (isLittleO_iff_tendsto (fun t ht =>
      (pow_ne_zero 2 (inv_ne_zero (hn t)) ht).elim)).mpr
    simpa only [one_div, ← inv_pow, inv_inv, zero_pow (by decide : 2 ≠ 0)] using hz.pow 2

namespace PairEstimateData

/-- The two separations and branch-preserving distance get levels along one
common subsequence, using their respective threshold systems. -/
theorem exists_joint_order_levels (p : PairEstimateData) (hz : Tendsto p.eps atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ, ∃ kz kw kr : Fin 6,
      kz ≠ 0 ∧ kw ≠ 0 ∧ kr ≠ 0 ∧
      HasOrderLevel ((epsilonPositionScales p.eps p.eps_ne_zero hz).comp φ hφ.tendsto_atTop)
        (p.z ∘ φ) kz ∧
      HasOrderLevel ((epsilonPositionScales p.eps p.eps_ne_zero hz).comp φ hφ.tendsto_atTop)
        (p.w ∘ φ) kw ∧
      HasOrderLevel ((epsilonDistanceScales p.eps p.eps_ne_zero hz).comp φ hφ.tendsto_atTop)
        (p.radius ∘ φ) kr := by
  let s := epsilonPositionScales p.eps p.eps_ne_zero hz
  let d := epsilonDistanceScales p.eps p.eps_ne_zero hz
  let scales : Fin 3 → OrderScales := ![s, s, d]
  let pairVariables : Fin 3 → ℕ → ℂ := ![p.z, p.w, p.radius]
  have hb : ∀ i, pairVariables i =O[atTop] (scales i).upper := by
    intro i
    fin_cases i
    · exact p.z_upper
    · exact p.w_upper
    · exact p.radius_upper
  obtain ⟨φ, hφ, k, hk⟩ := exists_simultaneous_order_levels_for_scales scales pairVariables hb
  exact ⟨φ, hφ, k 0, k 1, k 2,
    (hk 0).ne_zero_of_lower_bound (p.z_lower.comp_tendsto hφ.tendsto_atTop),
    (hk 1).ne_zero_of_lower_bound (p.w_lower.comp_tendsto hφ.tendsto_atTop),
    (hk 2).ne_zero_of_lower_bound (p.radius_lower.comp_tendsto hφ.tendsto_atTop),
    hk 0, hk 1, hk 2⟩

theorem z_orderLevel_ne_zero (p : PairEstimateData) (hz : Tendsto p.eps atTop (𝓝 0))
    {k : Fin 6} (hk : HasOrderLevel (epsilonPositionScales p.eps p.eps_ne_zero hz) p.z k) :
    k ≠ 0 := hk.ne_zero_of_lower_bound p.z_lower

theorem w_orderLevel_ne_zero (p : PairEstimateData) (hz : Tendsto p.eps atTop (𝓝 0))
    {k : Fin 6} (hk : HasOrderLevel (epsilonPositionScales p.eps p.eps_ne_zero hz) p.w k) :
    k ≠ 0 := hk.ne_zero_of_lower_bound p.w_lower

theorem distance_orderLevel_ne_zero (p : PairEstimateData) (hz : Tendsto p.eps atTop (𝓝 0))
    {k : Fin 6} (hk : HasOrderLevel (epsilonDistanceScales p.eps p.eps_ne_zero hz) p.radius k) :
    k ≠ 0 := hk.ne_zero_of_lower_bound p.radius_lower

end PairEstimateData

end CentralConfigurations
