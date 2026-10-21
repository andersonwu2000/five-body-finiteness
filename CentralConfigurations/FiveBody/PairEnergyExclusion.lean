import CentralConfigurations.FiveBody.PairEnergyEnergy

namespace CentralConfigurations.FiveBody.PairEnergy
open Filter
open scoped Topology

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}

/-- AK D1 = Chang printed 5, on the same pair 01/triple 234 labels with
both colors exchanged. Every energy input is derived from the actual code. -/
theorem false_of_chang5
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0 < m i) (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
    (hd : l.diagramCode=fiveBodySourceDiagram 4)
    (_ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.potential=(I0:ℂ)) : False := by
  have hds : (l.swapBalanced hb).diagramCode=akDiagram false := by
    change DiagramCode.swap l.diagramCode=akDiagram false
    rw [hd]
    decide +kernel
  exact false_of_ak_diagram (l.swapBalanced hb) hm hds hphysical hI

/-- AK D4 = Chang printed 6, with exactly the same common labels and color
exchange as D1. The complete collapsing-triple residual is retained. -/
theorem false_of_chang6
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0 < m i) (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
    (hd : l.diagramCode=fiveBodySourceDiagram 5)
    (_ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.potential=(I0:ℂ)) : False := by
  have hds : (l.swapBalanced hb).diagramCode=akDiagram true := by
    change DiagramCode.swap l.diagramCode=akDiagram true
    rw [hd]
    decide +kernel
  exact false_of_ak_diagram (l.swapBalanced hb) hm hds hphysical hI

end CentralConfigurations.FiveBody.PairEnergy
