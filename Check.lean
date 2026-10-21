import CentralConfigurations.FiveBody.D2Regular.PositiveFiniteness

open CentralConfigurations

-- This client supplies only a fixed mass tuple and positivity.
example (m : Fin 5 → ℝ) (hm : ∀ i, 0 < m i) :
    Finite (PhysicalSimilarityClass 5 m) :=
  FiveBody.finite_physical_classes_of_five_positive_masses m hm

-- The printed declaration exposes every parameter and the proof's consumer.
#print CentralConfigurations.FiveBody.finite_physical_classes_of_five_positive_masses
#print CentralConfigurations.FiveBody.provedRemainingAnalyticCases

#print axioms CentralConfigurations.FiveBody.finite_physical_classes_of_five_positive_masses
#print axioms CentralConfigurations.FiveBody.provedRemainingAnalyticCases
#print axioms CentralConfigurations.FiveBody.d2_physicalSourceImpossible
#print axioms CentralConfigurations.FiveBody.D2.Regular.false_of_actual_d2
#print axioms CentralConfigurations.FiveBody.D2.HZero.PhysicalEulerLimit.not_centered_response_zero
#print axioms CentralConfigurations.FiveBody.D2.Resonance.PhysicalEulerLimit.transverse_ne_half
#print axioms CentralConfigurations.FiveBody.D2.Resonance.exists_physicalEulerLimit_exceptional_free
#print axioms CentralConfigurations.FiveBody.D8.false_of_chang7
#print axioms CentralConfigurations.FiveBody.Classification.completeRProduct_zero_of_surviving_source
