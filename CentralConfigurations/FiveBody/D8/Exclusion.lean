import CentralConfigurations.FiveBody.D8.LowerWing
import CentralConfigurations.FiveBody.D8.RetainedInertia
import CentralConfigurations.FiveBody.D8.EnergyGap

namespace CentralConfigurations.FiveBody.D8
open Filter
open scoped Topology

/-- Original AK D8, in the kernel-verified canonical Chang printed-7 roles.
Every phase, response estimate, cross cancellation and residual energy input
is derived from the actual balanced sequence and the fixed physical level. -/
theorem false_of_chang7 {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
    (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.potential=(I0:ℂ)) : False := by
  obtain ⟨heq,hab,hc⟩ := actual_mass_equalities l hm hd hb ha
  obtain ⟨U,hUn,hshape,hcu,φ,hφ,hU,hV,-⟩ := exists_upper_common_phase l hm hd
  let lφ := l.comp φ hφ.tendsto_atTop
  have hdφ : lφ.diagramCode=fiveBodySourceDiagram 6 := hd
  obtain ⟨E,F,G,hEn,hFn,hGn,ψ,hψ,hE,hF,hG⟩ := exists_lower_root_limits lφ hm hdφ
  let L := lφ.comp ψ hψ.tendsto_atTop
  have hdL : L.diagramCode=fiveBodySourceDiagram 6 := hd
  obtain ⟨hforce,hFG⟩ := lower_force_equations L hm hdL hab hE hF hG
  have hclosure := lower_metric_closure L hm hdL hab hEn hFn hGn hE hF hG
  have henergy := retained_lower_energy L hm hdL (fun t => hI (φ (ψ t))) hUn hFn hGn
    (hU.comp hψ.tendsto_atTop) (hV.comp hψ.tendsto_atTop) hF hG
  rw [← hab] at henergy
  exact lower_energy_impossible hm heq hab hc hphysical hEn hFn hGn hFG hclosure hforce henergy

end CentralConfigurations.FiveBody.D8
