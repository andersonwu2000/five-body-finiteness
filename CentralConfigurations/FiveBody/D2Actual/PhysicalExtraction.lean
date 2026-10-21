import CentralConfigurations.FiveBody.D2Actual.PairSystem
import CentralConfigurations.FiveBody.D2Actual.TransverseOne
import CentralConfigurations.FiveBody.D2Actual.SignedEulerMetric

namespace CentralConfigurations.FiveBody.D2
open Filter
open scoped Topology BigOperators

/-- Actual physical D2 data after the complete equal-cube and isotropic deletions.
The regular IFT and the three exceptional-stratum deletions are not fields. -/
structure PhysicalEulerLimit (m : Fin 5 → ℝ)
    (q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ)))
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (I0 : ℝ)
    extends ActualLimit m q l (I0 : ℂ) where
  signedEuler : SignedEulerMetric triangle
  nonisotropic : (∑ i : Fin 3, (m (i.castLE (by decide)) : ℂ)*triangle.w i^2) ≠ 0
  transverse_ne_one : transverseEigenvalue triangle ≠ 1

theorem exists_physicalEulerLimit {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0 < m i) (hd : l.diagramCode = fiveBodySourceDiagram 17)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.potential = (I0 : ℂ)) :
    Nonempty (PhysicalEulerLimit m q l I0) := by
  obtain ⟨s⟩ := exists_actualLimit l hm hd ha hI
  obtain ⟨κ,hκ,hshape,hS⟩ := s.euler_nonisotropic hm hphysical
  obtain ⟨signed⟩ := exists_signedEulerMetric s.triangle hκ hshape
  exact ⟨{
    toActualLimit := s
    signedEuler := signed
    nonisotropic := hS
    transverse_ne_one := s.transverse_ne_one hm hphysical }⟩

end CentralConfigurations.FiveBody.D2
