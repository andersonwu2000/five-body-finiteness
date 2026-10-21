import CentralConfigurations.FiveBody.D2HZero.Exclusion

namespace CentralConfigurations.FiveBody.D2.HZero
open Filter
open scoped Topology

theorem exists_physicalEulerLimit_nonzero_response {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0 < m i) (hd : l.diagramCode=fiveBodySourceDiagram 17)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.potential=(I0 : ℂ)) :
    ∃ s : PhysicalEulerLimit m q l I0,
      transverseEigenvalue s.triangle ≠ 0 ∧
        ∃ i, centeredCrossResponse s.toFiveBodySource18Certificate i ≠ 0 := by
  obtain ⟨s,hell⟩ := EllZero.exists_physicalEulerLimit_transverse_ne_zero l hm hd ha hphysical hI
  exact ⟨s,hell,PhysicalEulerLimit.exists_centered_response_ne_zero s hm⟩

end CentralConfigurations.FiveBody.D2.HZero
