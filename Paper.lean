import CentralConfigurations.FiveBody.Source19Geometry
import CentralConfigurations.FiveBody.Source19Mass
import CentralConfigurations.Asymptotics.FourProductAlgebra
import CentralConfigurations.Asymptotics.FourProductDominance
import CentralConfigurations.Asymptotics.OneColor
import CentralConfigurations.Asymptotics.PairEstimates
import CentralConfigurations.Asymptotics.TwoSelection
import CentralConfigurations.Diagrams.GraphComponents
import CentralConfigurations.Enumeration.FiveBodySixteen
import CentralConfigurations.FiveBody.ClassifiedPhysicalFiniteness
import CentralConfigurations.FiveBody.D2Regular.PositiveFiniteness
import CentralConfigurations.FiveBody.D5MetricBound
import CentralConfigurations.FiveBody.D5RProduct
import CentralConfigurations.FiveBody.D6Butterfly.CommonOrders
import CentralConfigurations.FiveBody.D6Butterfly.Exclusion
import CentralConfigurations.FiveBody.D6Butterfly.Translations
import CentralConfigurations.FiveBody.D6Butterfly.WingOrders
import CentralConfigurations.FiveBody.D6Butterfly.WingRigidity
import CentralConfigurations.FiveBody.FixedLevelPhysicalFiniteness
import CentralConfigurations.FiveBody.OrdinaryDiagramIdentity
import CentralConfigurations.FiveBody.PhysicalPotentialFloor
import CentralConfigurations.FiveBody.RZeroCard
import CentralConfigurations.FiveBody.SimpleMassRelations
import CentralConfigurations.Model.PhysicalCoordinates
import CentralConfigurations.Model.PhysicalNormalization
import CentralConfigurations.Model.PotentialFiniteness

/-!
# Numbered statements in the accompanying paper
Run `lake env lean Paper.lean` from the package root.
Numbers correspond to the 2026-10-09 edition; stable LaTeX labels follow each number.
`#check` exposes the original type and verifies that the declaration exists.
It does not automatically certify equivalence with a prose statement.
The classification follows the twenty-source enumeration and four order exclusions. The D6 estimates are indexed before the mass relation.
-/

/- 1.1 | thm:main | Main finiteness theorem
-/
#check CentralConfigurations.FiveBody.finite_physical_classes_of_five_positive_masses

/- 2.1 | lem:normalization | Positive normalization
Normalization uses CenteredPhysicalSystem; see the original statement and the physical-coordinate bridge.
-/
#check CentralConfigurations.PhysicalCentralConfiguration.multiplier_pos
#check CentralConfigurations.RealCentralSystem.exists_positive_normalization

/- 2.2 | lem:floor | Physical potential floor
-/
#check CentralConfigurations.weighted_inverse_cubic
#check CentralConfigurations.NormalizedSystem.physicalPotentialLevel

/- 3.1 | lem:values | Finite potential values
-/
#check CentralConfigurations.NormalizedSystem.finite_potential_values

/- 4.1 | lem:recovery | Finite recovery from four-products
-/
#check CentralConfigurations.finite_gauged_five_body_of_finite_four_products
#check CentralConfigurations.five_body_four_product_recovery

/- 5.1 | prop:selection | Two-selection principle
-/
#check CentralConfigurations.finite_affine_set_of_two_selections

/- 6.1 | thm:classification | Sixteen-diagram classification
The source-index set and all sixteen AK masks are connected by exact finite identities; printed graph transcription remains a source-reading task.
-/
#check CentralConfigurations.ScaledZWLimit.five_body_source_orbit
#check CentralConfigurations.OrderedDiagramRealization.five_body_source_index_survives
#check CentralConfigurations.ScaledZWLimit.five_body_surviving_source_realization
#check CentralConfigurations.FiveBody.Ordinary.ak_to_chang_identity
#check CentralConfigurations.FiveBody.Ordinary.chang_to_ak_identity
#check CentralConfigurations.FiveBody.Ordinary.chang_indices_exact_survivors

/- 6.4 | lem:edgescales | Edge scales
Collection of estimates, not a single packaged theorem with the six paper clauses.
-/
#check CentralConfigurations.PairEstimateData.estimate_one
#check CentralConfigurations.PairEstimateData.estimate_two
#check CentralConfigurations.PairEstimateData.single_z_separations

/- 6.5 | lem:isolated | Isolated color components
Supporting component statements; the paper combines the force sum and circle argument.
-/
#check CentralConfigurations.OneColorLimit.coincident_component_circles_zero
#check CentralConfigurations.OneColorLimit.matrix_isolated_force

/- 6.6 | lem:D5mass | D5 mass relation
-/
#check CentralConfigurations.ScaledZWLimit.five_body_source3_reciprocal_mass_cases

/- 7.1 | hyp:decay | Physical-level pole decay
The first theorem has a RemainingAnalyticCases premise, discharged by the second.
-/
#check CentralConfigurations.FiveBody.Classification.fixed_level_decay_of_remaining_cases
#check CentralConfigurations.FiveBody.provedRemainingAnalyticCases

/- 7.2 | thm:conditional | Global reduction
-/
#check CentralConfigurations.finite_physical_classes_of_fixed_level_decay

/- 8.1 | lem:six | Six-factor bound
-/
#check CentralConfigurations.FiveBody.RZero.completeR_card_le_six

/- 9.1 | lem:d5 | Three-point collapsing cluster
The generic scale lemma is supported by norm_product_small; metric_small_of_akD5 applies it to the classified sequence. These are not interchangeable hypotheses.
-/
#check CentralConfigurations.FiveBody.D5.norm_product_small
#check CentralConfigurations.FiveBody.D5.metric_small_of_akD5

/- 9.2 | cor:d5 | D5 product decay
-/
#check CentralConfigurations.FiveBody.D5.completeRProduct_tendsto_zero_of_chang3

/- 13.1 | prop:D6 | D6 exclusion
-/
#check CentralConfigurations.FiveBody.D6.false_of_chang19

/- 13.2 | lem:D6shared | Short-coordinate and shared-vertex torque estimates
Direct short-coordinate and short-force estimates followed by the exact torque identity, all before equal pair masses. Apply the common relabeling and color exchange chang19_to_akD6; inverseScale corresponds to R^(-1). The paper derives the remaining force sums from the body-5 equations. The equal-mass conclusion is downstream in five_body_source19_mass_relation.
-/
#check CentralConfigurations.ScaledZWLimit.five_body_source19_small_center_and_forces
#check CentralConfigurations.five_body_cross_torque_identity
#check CentralConfigurations.five_body_cross_torque_bigO_square
#check CentralConfigurations.ScaledZWLimit.five_body_source19_cross_torque_limit
#check CentralConfigurations.ScaledZWLimit.five_body_source19_mass_relation

/- 13.3 | lem:D6rigid | Wing rigidity
-/
#check CentralConfigurations.FiveBody.D6.wing_rigidity
#check CentralConfigurations.FiveBody.D6.wing_cube_orders

/- 13.4 | lem:D6drift | First-order drifts
-/
#check CentralConfigurations.FiveBody.D6.outer_translation_orders
#check CentralConfigurations.FiveBody.D6.all_translation_orders
#check CentralConfigurations.FiveBody.D6.internal_force_orders

namespace CentralConfigurations.Paper

/-- Theorem 1.1: an explicitly typed paper-facing statement. -/
theorem main (m : Fin 5 → ℝ) (hm : ∀ i, 0 < m i) :
    Finite (PhysicalSimilarityClass 5 m) :=
  FiveBody.finite_physical_classes_of_five_positive_masses m hm

/-- Lemma 3.1: the complex finite-potential assertion. -/
theorem finite_potential (m : Fin 5 → ℂ) :
    (Set.range (fun q : NormalizedSystem ℂ 5 m => q.unorderedPotential)).Finite :=
  NormalizedSystem.finite_potential_values m

/-- Lemma 8.1: the complete exceptional index set has at most six members. -/
theorem six_factors (m : Fin 5 → ℝ) (hm : ∀ i, 0 < m i) :
    (FiveBody.RZero.completeR m).card ≤ 6 :=
  FiveBody.RZero.completeR_card_le_six m hm

end CentralConfigurations.Paper

#print axioms CentralConfigurations.Paper.main
#print axioms CentralConfigurations.Paper.finite_potential
#print axioms CentralConfigurations.Paper.six_factors
