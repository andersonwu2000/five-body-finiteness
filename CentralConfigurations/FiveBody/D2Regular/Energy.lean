import CentralConfigurations.FiveBody.D2Regular.Centers

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000

namespace ActualChart
variable {m : Fin 5 → ℂ} (s : ActualChart m)

/-- Before using the global centroid, both cluster products remain explicit. -/
theorem two_centroid_inertia :
    s.point.toNormalized.potential=
      m 3*m 4*pairMass m*s.beta+
      (∑ i : Fin 3, m (tripleIndex i)*s.c i*s.d i)+
      pairMass m*pairCenter m s.point.z*pairCenter m s.point.w+
      tripleMass m*tripleCenter m s.point.z*tripleCenter m s.point.w := by
  rw [PairEnergy.zw_potential]
  have hp := s.pair_difference
  field_simp [s.time_ne] at hp
  dsimp [beta,c,d]
  simp only [Fin.sum_univ_succ]
  dsimp [tripleIndex,pairCenter,tripleCenter]
  field_simp [s.pairMass_ne,s.tripleMass_ne,s.time_ne]
  dsimp [pairMass,tripleMass] at hp ⊢
  linear_combination (m 0+m 1+m 2)^2*m 3*m 4*(s.point.w 4-s.point.w 3)*hp

theorem centroid_product (hM : pairMass m+tripleMass m≠0) :
    pairMass m*pairCenter m s.point.z*pairCenter m s.point.w+
      tripleMass m*tripleCenter m s.point.z*tripleCenter m s.point.w=
      (pairMass m*tripleMass m)/(pairMass m+tripleMass m)*s.time^4*s.etaZ*s.etaW := by
  dsimp [etaZ,etaW]
  field_simp [hM,s.time_ne]
  linear_combination (pairMass m*pairCenter m s.point.w+
    tripleMass m*tripleCenter m s.point.w)*s.z_center_balance

/-- Full exact inertia, with the center remainder retained and no limiting argument. -/
theorem full_inertia (hM : pairMass m+tripleMass m≠0) :
    s.point.toNormalized.potential=
      m 3*m 4*pairMass m*s.beta+
      (∑ i : Fin 3, m (tripleIndex i)*s.c i*s.d i)+
      (pairMass m*tripleMass m)/(pairMass m+tripleMass m)*s.time^4*s.etaZ*s.etaW := by
  rw [s.two_centroid_inertia]
  rw [← s.centroid_product hM]
  ring

theorem potential_split :
    s.point.toNormalized.potential=m 3*m 4*s.point.delta 3 4+
      (m 0*m 1*s.point.delta 0 1+m 0*m 2*s.point.delta 0 2+m 1*m 2*s.point.delta 1 2)+
      s.time*(∑ p : Fin 2, ∑ i : Fin 3,
        m (pairIndex p)*m (tripleIndex i)*s.cross p i) := by
  rw [five_potential_split]
  dsimp [cross,pairIndex,tripleIndex]
  simp only [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro i _
  field_simp [s.time_ne]

end ActualChart
end
end CentralConfigurations.FiveBody.D2.Regular
