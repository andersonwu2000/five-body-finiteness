import CentralConfigurations.FiveBody.D2Regular.ActualRegular
import CentralConfigurations.FiveBody.D2Jacobian.Invertibility
import CentralConfigurations.FiveBody.D2Resonance.Extraction

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter
open scoped Topology

/-- The regular actual D2 branch is impossible. The strict local Jacobian,
its selected rows, all root sheets, and the original torque response are proved. -/
theorem false_of_physicalEulerLimit_regular {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
    {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
    (s : PhysicalEulerLimit m q l I0) (hm : ∀ i, 0<m i)
    (hell : transverseEigenvalue s.triangle≠0)
    (hhalf : transverseEigenvalue s.triangle≠ -(1/2:ℂ)) : False := by
  obtain ⟨e⟩ := exists_gaugeExtraction s.toActualLimit hm
  apply false_of_regular_jacobian s e hm hell (regularJacobian s e hm hhalf)
    (regularJacobian_strictFDerivAt s e hm hhalf)
  · intro v
    change ((regularJacobian s e hm hhalf : ChartSpace →L[ℂ] ChartSpace) v).2 2=_
    rw [regularJacobian_eq]
    exact augmentedJacobian_row_two s e v
  · intro v
    change ((regularJacobian s e hm hhalf : ChartSpace →L[ℂ] ChartSpace) v).2 3=_
    rw [regularJacobian_eq]
    exact augmentedJacobian_row_three s e v

/-- Actual Chang printed18 / AK D2 exclusion on the same physical potential
level, after the already proved exhaustive exceptional-stratum deletions. -/
theorem false_of_actual_d2 {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 17)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.potential=(I0:ℂ)) : False := by
  obtain ⟨s,hell,hhalf,_⟩ := Resonance.exists_physicalEulerLimit_exceptional_free
    l hm hd ha hphysical hI
  exact false_of_physicalEulerLimit_regular s hm hell hhalf

end
end CentralConfigurations.FiveBody.D2.Regular
