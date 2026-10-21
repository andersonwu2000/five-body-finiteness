import CentralConfigurations.FiveBody.D2Resonance.Exclusion

namespace CentralConfigurations.FiveBody.D2.Resonance
open Filter
open scoped Topology

theorem exists_physicalEulerLimit_exceptional_free {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 17)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀t, (q t).toNormalized.potential=(I0:ℂ)) :
    ∃ s : PhysicalEulerLimit m q l I0,
      transverseEigenvalue s.triangle≠0 ∧
      transverseEigenvalue s.triangle≠-(1/2:ℂ) ∧
      ∃ i, HZero.centeredCrossResponse s.toFiveBodySource18Certificate i≠0 := by
  obtain ⟨s,hzero,hresponse⟩ := HZero.exists_physicalEulerLimit_nonzero_response l hm hd ha hphysical hI
  exact ⟨s,hzero,PhysicalEulerLimit.transverse_ne_half s hm,hresponse⟩

end CentralConfigurations.FiveBody.D2.Resonance
