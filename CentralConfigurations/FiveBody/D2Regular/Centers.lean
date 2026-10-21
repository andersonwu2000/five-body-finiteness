import CentralConfigurations.FiveBody.D2Regular.Chart
import CentralConfigurations.FiveBody.PairEnergyInertia

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000

theorem cluster_center_balance {m v : Fin 5 → ℂ}
    (hA : pairMass m≠0) (hB : tripleMass m≠0)
    (hv : (∑ i, m i*v i)=0) :
    pairMass m*pairCenter m v+tripleMass m*tripleCenter m v=0 := by
  dsimp [pairCenter,tripleCenter]
  field_simp [hA,hB]
  simp [Fin.sum_univ_succ] at hv
  linear_combination hv

theorem cluster_force_sum {m v : Fin 5 → ℂ} (delta : Fin 5 → Fin 5 → ℂ)
    (hs : delta 4 3=delta 3 4)
    (hf : ∀ p : Fin 2, v (pairIndex p)=
      ∑ j, m j*delta (pairIndex p) j^3*(v (pairIndex p)-v j)) :
    m 3*v 3+m 4*v 4=
      ∑ p : Fin 2, ∑ i : Fin 3,
        m (pairIndex p)*m (tripleIndex i)*delta (pairIndex p) (tripleIndex i)^3*
          (v (pairIndex p)-v (tripleIndex i)) := by
  have h0 := hf 0
  have h1 := hf 1
  simp only [Fin.sum_univ_succ,pairIndex,tripleIndex] at h0 h1 ⊢
  dsimp at h0 h1 ⊢
  rw [hs] at h1
  linear_combination m 3*h0+m 4*h1

namespace ActualChart
variable {m : Fin 5 → ℂ} (s : ActualChart m)

def crossSumZ : ℂ := ∑ p : Fin 2, ∑ i : Fin 3,
  m (pairIndex p)*m (tripleIndex i)*s.cross p i^3*s.zeta p i
def crossSumW : ℂ := ∑ p : Fin 2, ∑ i : Fin 3,
  m (pairIndex p)*m (tripleIndex i)*s.cross p i^3*s.chi p i

theorem z_center_balance :
    pairMass m*pairCenter m s.point.z+tripleMass m*tripleCenter m s.point.z=0 :=
  cluster_center_balance s.pairMass_ne s.tripleMass_ne s.point.mass_center_z

theorem w_center_balance :
    pairMass m*pairCenter m s.point.w+tripleMass m*tripleCenter m s.point.w=0 :=
  cluster_center_balance s.pairMass_ne s.tripleMass_ne s.point.mass_center_w

theorem pair_center_z : pairCenter m s.point.z= -s.time^2*s.crossSumZ/pairMass m := by
  have hf := cluster_force_sum s.point.delta (s.point.delta_symm 4 3)
    (fun p => s.point.force_z (pairIndex p))
  dsimp [crossSumZ]
  simp_rw [s.zeta_eq]
  dsimp [cross,pairCenter]
  simp only [Fin.sum_univ_succ] at hf ⊢
  field_simp [s.pairMass_ne,s.time_ne]
  linear_combination hf

theorem pair_center_w : pairCenter m s.point.w= -s.time^2*s.crossSumW/pairMass m := by
  have hf := cluster_force_sum s.point.delta (s.point.delta_symm 4 3)
    (fun p => s.point.force_w (pairIndex p))
  dsimp [crossSumW]
  simp_rw [s.chi_eq]
  dsimp [cross,pairCenter]
  simp only [Fin.sum_univ_succ] at hf ⊢
  field_simp [s.pairMass_ne,s.time_ne]
  linear_combination hf

theorem triple_center_z : tripleCenter m s.point.z=s.time^2*s.crossSumZ/tripleMass m := by
  have hh := s.z_center_balance
  rw [s.pair_center_z] at hh
  field_simp [s.pairMass_ne] at hh
  apply (eq_div_iff s.tripleMass_ne).2
  linear_combination hh

theorem triple_center_w : tripleCenter m s.point.w=s.time^2*s.crossSumW/tripleMass m := by
  have hh := s.w_center_balance
  rw [s.pair_center_w] at hh
  field_simp [s.pairMass_ne] at hh
  apply (eq_div_iff s.tripleMass_ne).2
  linear_combination hh

theorem etaZ_equation :
    s.etaZ=(pairMass m+tripleMass m)/(pairMass m*tripleMass m)*s.crossSumZ := by
  dsimp [etaZ]
  rw [s.triple_center_z,s.pair_center_z]
  field_simp [s.pairMass_ne,s.tripleMass_ne,s.time_ne]
  ring

theorem etaW_equation :
    s.etaW=(pairMass m+tripleMass m)/(pairMass m*tripleMass m)*s.crossSumW := by
  dsimp [etaW]
  rw [s.triple_center_w,s.pair_center_w]
  field_simp [s.pairMass_ne,s.tripleMass_ne,s.time_ne]
  ring

end ActualChart
end
end CentralConfigurations.FiveBody.D2.Regular
