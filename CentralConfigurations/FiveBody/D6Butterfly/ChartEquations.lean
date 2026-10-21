import CentralConfigurations.FiveBody.D6Butterfly.WingOrders

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology BigOperators
noncomputable section

variable {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q)

def PairGauge.crossRoot (e : Fin 4) : ℂ := q.delta (crossLeft e) (crossRight e)/g.time
def PairGauge.internalZ : ℂ :=
  mass 0*q.delta 0 2^3*(g.coeff 4-g.coeff 2)+mass 1*q.delta 1 2^3*(g.coeff 4-g.coeff 3)
def PairGauge.internalW : ℂ :=
  mass 3*q.delta 2 3^3*(g.coeff 5-g.coeff 6)+mass 4*q.delta 2 4^3*(g.coeff 5-g.coeff 7)

theorem PairGauge.center_z :
    mass 0*g.coeff 2+mass 1*g.coeff 3+mass 2*g.coeff 4+(mass 3+mass 4)*g.coeff 0=
      -(mass 3-mass 4)/g.time^2 := by
  have h := g.normalized.mass_center_z
  simp [Fin.sum_univ_succ] at h
  obtain ⟨h3,h4,-,-,h0,h1,h2,-,-,-⟩ := g.chart
  rw [h0,h1,h2,h3,h4] at h
  field_simp [g.time_ne] at h ⊢
  linear_combination h

theorem PairGauge.center_w :
    (mass 0+mass 1)*g.coeff 1+mass 2*g.coeff 5+mass 3*g.coeff 6+mass 4*g.coeff 7=
      -(mass 0-mass 1)/g.time^2 := by
  have h := g.normalized.mass_center_w
  simp [Fin.sum_univ_succ] at h
  obtain ⟨-,-,h0,h1,-,-,-,h2,h3,h4⟩ := g.chart
  rw [h0,h1,h2,h3,h4] at h
  field_simp [g.time_ne] at h ⊢
  linear_combination h

theorem PairGauge.torque_identity :
    fiveBodyCrossTorque g.normalized = mass 2*g.time^2*
      (g.coeff 5*g.coeff 4-g.coeff 5*g.internalZ-g.coeff 4*g.internalW) := by
  rw [five_body_cross_torque_identity]
  simp only [PairGauge.internalZ,PairGauge.internalW,ZWSystem.zForce,ZWSystem.wForce]
  change mass 2*((g.normalized.w 2*g.normalized.z 2)-
      g.normalized.w 2*(mass 0*(q.delta 2 0^3*(g.normalized.z 2-g.normalized.z 0))+
        mass 1*(q.delta 2 1^3*(g.normalized.z 2-g.normalized.z 1)))-
      g.normalized.z 2*(mass 3*(q.delta 2 3^3*(g.normalized.w 2-g.normalized.w 3))+
        mass 4*(q.delta 2 4^3*(g.normalized.w 2-g.normalized.w 4))))=_
  obtain ⟨-,-,-,-,h0,h1,h2,h3,h4,h5⟩ := g.chart
  rw [h0,h1,h2,h3,h4,h5,q.delta_symm 2 0,q.delta_symm 2 1]
  ring

theorem PairGauge.small_w3 :
    g.coeff 6=mass 4*q.delta 3 4^3*(g.coeff 6-g.coeff 7)+mass 2*q.delta 2 3^3*(g.coeff 6-g.coeff 5)+
      g.time*(-mass 0*g.crossRoot 0^3+mass 1*g.crossRoot 2^3)+
      g.time^3*(g.coeff 6-g.coeff 1)*(mass 0*g.crossRoot 0^3+mass 1*g.crossRoot 2^3) := by
  have h := g.normalized.force_w 3
  change g.normalized.w 3=∑ j, mass j*q.delta 3 j^3*(g.normalized.w 3-g.normalized.w j) at h
  simp [Fin.sum_univ_succ,q.delta_symm 3 0,q.delta_symm 3 1,q.delta_symm 3 2] at h
  obtain ⟨-,-,h0,h1,-,-,-,h2,h3,h4⟩ := g.chart
  rw [h0,h1,h2,h3,h4] at h
  dsimp [PairGauge.crossRoot,crossLeft,crossRight]
  field_simp [g.time_ne] at h ⊢
  linear_combination h

theorem PairGauge.small_w4 :
    g.coeff 7=mass 3*q.delta 3 4^3*(g.coeff 7-g.coeff 6)+mass 2*q.delta 2 4^3*(g.coeff 7-g.coeff 5)+
      g.time*(-mass 0*g.crossRoot 1^3+mass 1*g.crossRoot 3^3)+
      g.time^3*(g.coeff 7-g.coeff 1)*(mass 0*g.crossRoot 1^3+mass 1*g.crossRoot 3^3) := by
  have h := g.normalized.force_w 4
  change g.normalized.w 4=∑ j, mass j*q.delta 4 j^3*(g.normalized.w 4-g.normalized.w j) at h
  simp [Fin.sum_univ_succ,q.delta_symm 4 0,q.delta_symm 4 1,q.delta_symm 4 2,q.delta_symm 4 3] at h
  obtain ⟨-,-,h0,h1,-,-,-,h2,h3,h4⟩ := g.chart
  rw [h0,h1,h2,h3,h4] at h
  dsimp [PairGauge.crossRoot,crossLeft,crossRight]
  field_simp [g.time_ne] at h ⊢
  linear_combination h

theorem PairGauge.small_z0 :
    g.coeff 2=mass 1*q.delta 0 1^3*(g.coeff 2-g.coeff 3)+mass 2*q.delta 0 2^3*(g.coeff 2-g.coeff 4)+
      g.time*(-mass 3*g.crossRoot 0^3+mass 4*g.crossRoot 1^3)+
      g.time^3*(g.coeff 2-g.coeff 0)*(mass 3*g.crossRoot 0^3+mass 4*g.crossRoot 1^3) := by
  have h := g.normalized.force_z 0
  change g.normalized.z 0=∑ j, mass j*q.delta 0 j^3*(g.normalized.z 0-g.normalized.z j) at h
  simp [Fin.sum_univ_succ] at h
  obtain ⟨h3,h4,-,-,h0,h1,h2,-,-,-⟩ := g.chart
  rw [h0,h1,h2,h3,h4] at h
  dsimp [PairGauge.crossRoot,crossLeft,crossRight]
  field_simp [g.time_ne] at h ⊢
  linear_combination h

theorem PairGauge.small_z1 :
    g.coeff 3=mass 0*q.delta 0 1^3*(g.coeff 3-g.coeff 2)+mass 2*q.delta 1 2^3*(g.coeff 3-g.coeff 4)+
      g.time*(-mass 3*g.crossRoot 2^3+mass 4*g.crossRoot 3^3)+
      g.time^3*(g.coeff 3-g.coeff 0)*(mass 3*g.crossRoot 2^3+mass 4*g.crossRoot 3^3) := by
  have h := g.normalized.force_z 1
  change g.normalized.z 1=∑ j, mass j*q.delta 1 j^3*(g.normalized.z 1-g.normalized.z j) at h
  simp [Fin.sum_univ_succ,q.delta_symm 1 0] at h
  obtain ⟨h3,h4,-,-,h0,h1,h2,-,-,-⟩ := g.chart
  rw [h0,h1,h2,h3,h4] at h
  dsimp [PairGauge.crossRoot,crossLeft,crossRight]
  field_simp [g.time_ne] at h ⊢
  linear_combination h

end
end CentralConfigurations.FiveBody.D6

