import CentralConfigurations.FiveBody.PhysicalPotentialFloor
import CentralConfigurations.Enumeration.FiveBodySourceData
import CentralConfigurations.Asymptotics.Balancing
import CentralConfigurations.Enumeration.NormalizedSearch

/-!
# Interfaces for local diagram exclusions

PhysicalSourceImpossible expresses exclusion on a fixed physical potential
level. RemainingAnalyticCases records the D2 input to the classified case
analysis. D2Regular/PositiveFiniteness.lean constructs this input from the
local D2 proof.
-/

namespace CentralConfigurations.FiveBody.Classification
noncomputable section
open Filter
open scoped Topology

def PhysicalSourceImpossible (m : Fin 5 → ℝ) (k : Fin 20) : Prop :=
  ∀ q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ)),
    ∀ l : ScaledZWLimit q (fun t => (q t).inverseScale),
      (∀ i, 0 < m i) →
      (∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) →
      l.diagramCode = fiveBodySourceDiagram k →
      Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0) →
      ∀ I0 : ℝ, PhysicalPotentialLevel m I0 →
        (∀ t, (q t).toNormalized.potential = (I0 : ℂ)) → False

def SourceImpossible (m : Fin 5 → ℝ) (k : Fin 20) : Prop :=
  ∀ q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ)),
    ∀ l : ScaledZWLimit q (fun t => (q t).inverseScale),
      (∀ i, 0 < m i) →
      (∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) →
      l.diagramCode = fiveBodySourceDiagram k →
      Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0) → False

/-- Fixed masses keep their labels, even when numerical masses repeat.
One common permutation is allowed at every actual source extraction.
D2 retains the same fixed physical numerical potential. D6 and D8 are
proved actual-sequence exclusions. The raw code is Chang's source code. -/
structure RemainingAnalyticCases (m : Fin 5 → ℝ) : Prop where
  d2 : ∀ e : Equiv.Perm (Fin 5), PhysicalSourceImpossible (m ∘ e) 17

end
end CentralConfigurations.FiveBody.Classification
