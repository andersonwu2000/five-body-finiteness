import CentralConfigurations.FiveBody.D2Regular.Forces

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000

namespace ActualChart
variable {m : Fin 5 → ℂ} (s : ActualChart m)

theorem pair_internal_z (p : Fin 2) :
    (∑ r : Fin 2, m (pairIndex r)*s.point.delta (pairIndex p) (pairIndex r)^3*
      (s.point.z (pairIndex p)-s.point.z (pairIndex r)))=
      pairMass m*s.point.delta 3 4^3*s.a p/s.time := by
  simp_rw [s.pair_z]
  fin_cases p <;>
    simp [Fin.sum_univ_succ,a,pairIndex,s.point.delta_symm 4 3,pairMass]
  all_goals ring

theorem pair_internal_w (p : Fin 2) :
    (∑ r : Fin 2, m (pairIndex r)*s.point.delta (pairIndex p) (pairIndex r)^3*
      (s.point.w (pairIndex p)-s.point.w (pairIndex r)))=
      pairMass m*s.point.delta 3 4^3*s.time*s.b p := by
  simp_rw [s.pair_w]
  fin_cases p <;>
    simp [Fin.sum_univ_succ,a,b,pairIndex,s.point.delta_symm 4 3,pairMass]
  all_goals ring

theorem pair_z_residual (p : Fin 2) :
    (1-pairMass m*s.point.delta 3 4^3)*s.a p= -s.time^3*(s.Gz p-s.meanP s.Gz) := by
  have hs : s.point.z (pairIndex p)=
      (∑ r : Fin 2, m (pairIndex r)*s.point.delta (pairIndex p) (pairIndex r)^3*
        (s.point.z (pairIndex p)-s.point.z (pairIndex r)))-
      (∑ i : Fin 3, m (tripleIndex i)*s.point.delta (pairIndex p) (tripleIndex i)^3*
        (s.point.z (tripleIndex i)-s.point.z (pairIndex p))) := by
    have hf := s.point.force_z (pairIndex p)
    simp [Fin.sum_univ_succ,pairIndex,tripleIndex] at hf ⊢
    linear_combination hf
  rw [s.pair_internal_z p] at hs
  simp_rw [mul_assoc (m _),s.cross_z_force] at hs
  rw [s.pair_z p,s.pair_center_z] at hs
  rw [s.Gz_mean]
  dsimp [Gz]
  simp [Fin.sum_univ_succ] at hs ⊢
  field_simp [s.time_ne,s.pairMass_ne] at hs ⊢
  linear_combination hs

theorem pair_w_residual (p : Fin 2) :
    (1-pairMass m*s.point.delta 3 4^3)*s.b p= -s.time*(s.Gw p-s.meanP s.Gw) := by
  have hs : s.point.w (pairIndex p)=
      (∑ r : Fin 2, m (pairIndex r)*s.point.delta (pairIndex p) (pairIndex r)^3*
        (s.point.w (pairIndex p)-s.point.w (pairIndex r)))-
      (∑ i : Fin 3, m (tripleIndex i)*s.point.delta (pairIndex p) (tripleIndex i)^3*
        (s.point.w (tripleIndex i)-s.point.w (pairIndex p))) := by
    have hf := s.point.force_w (pairIndex p)
    simp [Fin.sum_univ_succ,pairIndex,tripleIndex] at hf ⊢
    linear_combination hf
  rw [s.pair_internal_w p] at hs
  simp_rw [mul_assoc (m _),s.cross_w_force] at hs
  rw [s.pair_w p,s.pair_center_w] at hs
  rw [s.Gw_mean]
  dsimp [Gw]
  simp [Fin.sum_univ_succ] at hs ⊢
  apply (mul_left_cancel₀ s.time_ne)
  field_simp [s.time_ne,s.pairMass_ne] at hs ⊢
  linear_combination hs

theorem pair_metric : s.point.delta 3 4^2*pairMass m^2*s.beta=1 := by
  have hh := s.point.distance 3 4 (by decide)
  change s.point.delta 3 4^2*((s.point.z (pairIndex 0)-s.point.z (pairIndex 1))*
    (s.point.w (pairIndex 0)-s.point.w (pairIndex 1)))=1 at hh
  rw [s.pair_z 0,s.pair_z 1,s.pair_w 0,s.pair_w 1] at hh
  dsimp [a,b] at hh
  field_simp [s.time_ne] at hh
  dsimp [pairMass]
  apply (mul_left_cancel₀ s.time_ne)
  linear_combination hh

end ActualChart
end
end CentralConfigurations.FiveBody.D2.Regular
