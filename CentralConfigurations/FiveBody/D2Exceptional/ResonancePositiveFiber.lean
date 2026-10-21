import CentralConfigurations.FiveBody.D2Exceptional.ResonanceCertificate

namespace CentralConfigurations.FiveBody.D2.Exceptional

theorem R10_pos {r : ℝ} (hr : 1 < r) : 0 < R10 r := by
  rw [R10_shift]
  have h : 0 < r-1 := sub_pos.mpr hr
  positivity

theorem coefficient_r_eq_two {u v r : ℝ} (hr : 1 < r)
    (h1 : F1 u v r=0) (h2 : F2 u v r=0) (h3 : F3 u v r=0) : r=2 := by
  have h := coefficient_elimination u v r h1 h2 h3
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (ne_of_gt (R10_pos hr)))

theorem coefficient_fiber_two {u v : ℝ}
    (h1 : F1 u v 2=0) (h2 : F2 u v 2=0) (h3 : F3 u v 2=0) :
    u=v ∧ v^2+2*v-1=0 := by
  dsimp [F1,F2,F3] at h1 h2 h3
  constructor
  · linear_combination (-v/7-4/21)*h1 + (25*v/42-3/7)*h2 + (-u/3-5*v/7+22/21)*h3
  · linear_combination (2*v/7-4/21)*h1 + (4/7-25*v/21)*h2 + (2*u/3+10*v/7-41/21)*h3

theorem coefficient_positive_fiber {u v r : ℝ} (hr : 1 < r) (hv : 0 < v)
    (h1 : F1 u v r=0) (h2 : F2 u v r=0) (h3 : F3 u v r=0) :
    r=2 ∧ u=Real.sqrt 2-1 ∧ v=Real.sqrt 2-1 := by
  have hr2 := coefficient_r_eq_two hr h1 h2 h3
  subst r
  obtain ⟨huv,hvpoly⟩ := coefficient_fiber_two h1 h2 h3
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have heq : (v+1)^2 = (Real.sqrt 2)^2 := by nlinarith
  have hvroot : v+1 = Real.sqrt 2 := by
    rcases (sq_eq_sq_iff_eq_or_eq_neg).mp heq with h | h
    · exact h
    · exfalso; linarith
  exact ⟨rfl, by linarith, by linarith⟩

end CentralConfigurations.FiveBody.D2.Exceptional
