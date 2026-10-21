import CentralConfigurations.FiveBody.D5FourProducts
import CentralConfigurations.FiveBody.RProductDecay

namespace CentralConfigurations.FiveBody.D5
open Filter Asymptotics
open scoped Topology BigOperators

/-- Actual canonical D5 makes the complete mass-only R product tend to zero.
The internal triple is established by the existing actual mass relation;
there is no supplied metric-bound or product-decay premise. -/
theorem completeRProduct_tendsto_zero_of_chang3
    {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0 < m i) (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (hd : l.diagramCode = fiveBodySourceDiagram 2)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.potential = (I0 : ℂ)) :
    Tendsto (fun t => (q t).toNormalized.fiveBodySelectedProduct (RZero.completeR m))
      atTop (𝓝 0) := by
  have ho := original_fourProduct_orders l hm hb hd ha hphysical hI
  have heps : Tendsto (fun t => (q t).epsilon) atTop (𝓝 0) := by
    have hh := (Complex.continuous_re.tendsto 0).comp (eps_zero ha)
    simpa only [eps,Complex.ofReal_re,Complex.zero_re] using hh
  exact RZero.selectedProduct_tendsto_zero_of_d5_orders m hm
    (fun t => (q t).toNormalized) (fun t => (q t).epsilon)
    (fun t => (q t).epsilon_pos 0 1 (by decide)) heps 0
    (RZero.d5_internal_mem_completeR m hm l hd) ho.1 (fun e _ he => ho.2 e he)

end CentralConfigurations.FiveBody.D5
