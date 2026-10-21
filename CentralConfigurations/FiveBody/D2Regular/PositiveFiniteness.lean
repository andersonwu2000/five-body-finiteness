import CentralConfigurations.FiveBody.D2Regular.Exclusion
import CentralConfigurations.FiveBody.ClassifiedPhysicalFiniteness

namespace CentralConfigurations.FiveBody

/-- D2 exclusion (Chang diagram 18, source index 17) on a fixed
physical potential level. The balancing premise is accepted by the common
classification interface and is not needed by the local D2 exclusion. -/
theorem d2_physicalSourceImpossible (m : Fin 5 → ℝ) :
    Classification.PhysicalSourceImpossible m 17 := by
  intro q l hm _hb hd ha I0 hphysical hI
  exact D2.Regular.false_of_actual_d2 l hm hd ha hphysical hI

/-- The D2 exclusion supplies the local case-analysis interface in every
common labeling. -/
theorem provedRemainingAnalyticCases (m : Fin 5 → ℝ) :
    Classification.RemainingAnalyticCases m where
  d2 e := d2_physicalSourceImpossible (m ∘ e)

/-- Finitely many planar physical similarity classes for five labelled
positive masses, including coincident numerical masses. -/
theorem finite_physical_classes_of_five_positive_masses (m : Fin 5 → ℝ)
    (hm : ∀ i, 0<m i) : Finite (PhysicalSimilarityClass 5 m) :=
  Classification.finite_physical_classes_of_remaining_cases m hm
    (provedRemainingAnalyticCases m) 0 1 (by decide)

end CentralConfigurations.FiveBody
