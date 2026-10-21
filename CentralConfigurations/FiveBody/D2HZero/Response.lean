import CentralConfigurations.FiveBody.D2EllZero.Exclusion

namespace CentralConfigurations.FiveBody.D2.HZero
open scoped BigOperators

noncomputable def crossCombination {m : Fin 5 → ℝ}
    (s : FiveBodySource18Certificate m) (i : Fin 3) : ℂ :=
  (m 3 : ℂ)*s.cross 0 i+(m 4 : ℂ)*s.cross 1 i

noncomputable def crossResponse {m : Fin 5 → ℝ}
    (s : FiveBodySource18Certificate m) (i : Fin 3) : ℂ :=
  crossCombination s i/s.triangle.w i

/-- The supplied triple-centered vector of B_i / w_i, with the original six roots. -/
noncomputable def centeredCrossResponse {m : Fin 5 → ℝ}
    (s : FiveBodySource18Certificate m) (i : Fin 3) : ℂ :=
  crossResponse s i-
    (∑ j : Fin 3, (m (j.castLE (by decide)) : ℂ)*crossResponse s j)/
      (∑ j : Fin 3, (m (j.castLE (by decide)) : ℂ))

theorem exists_cross_multiple_of_zero {m : Fin 5 → ℝ}
    (s : FiveBodySource18Certificate m) (hzero : ∀ i, centeredCrossResponse s i=0) :
    ∃ K : ℂ, ∀ i, crossCombination s i=K*s.triangle.w i := by
  let K : ℂ := (∑ j : Fin 3, (m (j.castLE (by decide)) : ℂ)*crossResponse s j)/
    (∑ j : Fin 3, (m (j.castLE (by decide)) : ℂ))
  refine ⟨K,?_⟩
  intro i
  have h := hzero i
  change crossResponse s i-K=0 at h
  exact (div_eq_iff (s.w_ne_zero i)).mp (sub_eq_zero.mp h)

end CentralConfigurations.FiveBody.D2.HZero
