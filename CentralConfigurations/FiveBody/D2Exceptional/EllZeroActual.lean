import CentralConfigurations.FiveBody.D2Exceptional.GapClear
import CentralConfigurations.FiveBody.D2Exceptional.EllZeroMass
import CentralConfigurations.FiveBody.D2Actual.PhysicalExtraction

namespace CentralConfigurations.FiveBody.D2.Exceptional

/-- The three real positive mass kernels, with the actual gap and signed roots retained. -/
def EllZeroCases {m : Fin 3 → ℝ} {r : ZWSystem ℂ 3 (fun i => (m i : ℂ))}
    (d : GapData r) : Prop :=
  (d.sign13=1 ∧ d.sign23=1 ∧ RankK0 d.x=0 ∧ m 0=m 2 ∧ m 1=5*m 0) ∨
  (d.sign13=1 ∧ d.sign23=-1 ∧ RankK1 d.x=0 ∧ m 0=m 1 ∧ m 2=5*m 0) ∨
  (d.sign13=-1 ∧ d.sign23=-1 ∧ RankK3 d.x=0 ∧ m 0=5*m 1 ∧ m 1=m 2)

theorem GapData.ell_zero_cases {m : Fin 3 → ℝ}
    {r : ZWSystem ℂ 3 (fun i => (m i : ℂ))} (d : GapData r)
    (hM : m 0+m 1+m 2 ≠ 0) (hell : transverseEigenvalue r=0) : EllZeroCases d := by
  have hE := d.euler_zero
  have hT := d.trace_zero hell
  rcases d.sign13_values with h13 | h13 <;> rcases d.sign23_values with h23 | h23
  · rw [h13,h23] at hE hT
    have hP : GapP0 (m 0) (m 1) (m 2) d.x=0 := by
      rw [clear_euler0 _ _ _ _ d.x_ne_zero d.x_ne_one,hE,mul_zero]
    have hQ : GapQ0 (m 0) (m 1) (m 2) d.x=0 := by
      rw [clear_trace0 _ _ _ _ d.x_ne_zero d.x_ne_one,hT,mul_zero]
    obtain ⟨hk,ha,hb⟩ := mass_kernel0 hM d.x_ne_zero d.x_ne_one hP hQ
    exact Or.inl ⟨h13,h23,hk,ha,hb⟩
  · rw [h13,h23] at hE hT
    have hP : GapP1 (m 0) (m 1) (m 2) d.x=0 := by
      rw [clear_euler1 _ _ _ _ d.x_ne_zero d.x_ne_one,hE,mul_zero]
    have hQ : GapQ1 (m 0) (m 1) (m 2) d.x=0 := by
      rw [clear_trace1 _ _ _ _ d.x_ne_zero d.x_ne_one,hT,mul_zero]
    obtain ⟨hk,ha,hc⟩ := mass_kernel1 hM d.x_ne_zero d.x_ne_one hP hQ
    exact Or.inr (Or.inl ⟨h13,h23,hk,ha,hc⟩)
  · rw [h13,h23] at hE hT
    have hP : GapP2 (m 0) (m 1) (m 2) d.x=0 := by
      rw [clear_euler2 _ _ _ _ d.x_ne_zero d.x_ne_one,hE,mul_zero]
    have hQ : GapQ2 (m 0) (m 1) (m 2) d.x=0 := by
      rw [clear_trace2 _ _ _ _ d.x_ne_zero d.x_ne_one,hT,mul_zero]
    have hMC : (m 0 : ℂ)+m 1+m 2 ≠ 0 := by exact_mod_cast hM
    exact (no_nonzero_mass_kernel2 hMC d.x_ne_zero d.x_ne_one hP hQ).elim
  · rw [h13,h23] at hE hT
    have hP : GapP3 (m 0) (m 1) (m 2) d.x=0 := by
      rw [clear_euler3 _ _ _ _ d.x_ne_zero d.x_ne_one,hE,mul_zero]
    have hQ : GapQ3 (m 0) (m 1) (m 2) d.x=0 := by
      rw [clear_trace3 _ _ _ _ d.x_ne_zero d.x_ne_one,hT,mul_zero]
    obtain ⟨hk,ha,hb⟩ := mass_kernel3 hM d.x_ne_zero d.x_ne_one hP hQ
    exact Or.inr (Or.inr ⟨h13,h23,hk,ha,hb⟩)

theorem actual_ell_zero_mass_cases {m : Fin 3 → ℝ}
    {r : ZWSystem ℂ 3 (fun i => (m i : ℂ))} (s : SignedEulerMetric r)
    (hm : ∀ i, 0 < m i) (hell : transverseEigenvalue r=0) :
    ∃ d : GapData r, EllZeroCases d := by
  obtain ⟨d⟩ := exists_gapData s
  exact ⟨d,d.ell_zero_cases (ne_of_gt (by linarith [hm 0,hm 1,hm 2])) hell⟩

theorem physical_ell_zero_mass_cases {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
    (s : PhysicalEulerLimit m q l I0) (hm : ∀ i, 0 < m i)
    (hell : transverseEigenvalue s.triangle=0) :
    ∃ d : GapData s.triangle, EllZeroCases d := by
  exact actual_ell_zero_mass_cases s.signedEuler
    (fun i => hm (i.castLE (by decide))) hell

end CentralConfigurations.FiveBody.D2.Exceptional
