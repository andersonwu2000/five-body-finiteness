import CentralConfigurations.FiveBody.D6Butterfly.CrossRigidity

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology BigOperators
noncomputable section

variable {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q)

def PairGauge.crossZ := mass 0*g.normalized.zForce 3 0+mass 1*g.normalized.zForce 3 1
def PairGauge.crossW := mass 3*g.normalized.wForce 0 3+mass 4*g.normalized.wForce 0 4

theorem PairGauge.wing_difference_z :
    mass 3*q.delta 2 3^3-mass 4*q.delta 2 4^3 = g.time^2*(
      mass 0*q.delta 0 2^3*(g.coeff 4-g.coeff 2)+mass 1*q.delta 1 2^3*(g.coeff 4-g.coeff 3)+
      (mass 3*q.delta 2 3^3+mass 4*q.delta 2 4^3)*(g.coeff 4-g.coeff 0)-g.coeff 4) := by
  have h := g.normalized.force_z 2
  change g.normalized.z 2=∑ j, mass j*q.delta 2 j^3*(g.normalized.z 2-g.normalized.z j) at h
  simp [Fin.sum_univ_succ,q.delta_symm 2 0,q.delta_symm 2 1] at h
  obtain ⟨h3,h4,-,-,h0,h1,h2,-,-,-⟩ := g.chart
  rw [h0,h1,h2,h3,h4] at h
  field_simp [g.time_ne] at h
  linear_combination h

theorem PairGauge.wing_difference_w :
    mass 0*q.delta 0 2^3-mass 1*q.delta 1 2^3 = g.time^2*(
      mass 3*q.delta 2 3^3*(g.coeff 5-g.coeff 6)+mass 4*q.delta 2 4^3*(g.coeff 5-g.coeff 7)+
      (mass 0*q.delta 0 2^3+mass 1*q.delta 1 2^3)*(g.coeff 5-g.coeff 1)-g.coeff 5) := by
  have h := g.normalized.force_w 2
  change g.normalized.w 2=∑ j, mass j*q.delta 2 j^3*(g.normalized.w 2-g.normalized.w j) at h
  simp [Fin.sum_univ_succ,q.delta_symm 2 0,q.delta_symm 2 1] at h
  obtain ⟨-,-,h0,h1,-,-,-,h2,h3,h4⟩ := g.chart
  rw [h0,h1,h2,h3,h4] at h
  field_simp [g.time_ne] at h
  linear_combination h

theorem PairGauge.wing_normalization_z :
    2*mass 4*q.delta 3 4^3+mass 2*q.delta 2 3^3-1 =
      g.time^2*(g.coeff 0-mass 2*q.delta 2 3^3*(g.coeff 0-g.coeff 4))-g.time*g.crossZ := by
  have h := g.normalized.force_z 3
  change g.normalized.z 3=∑ j, mass j*q.delta 3 j^3*(g.normalized.z 3-g.normalized.z j) at h
  simp [Fin.sum_univ_succ,q.delta_symm 3 2] at h
  have he : g.crossZ=mass 0*q.delta 3 0^3*(g.normalized.z 3-g.normalized.z 0)+
      mass 1*q.delta 3 1^3*(g.normalized.z 3-g.normalized.z 1) := by
    change mass 0*(q.delta 3 0^3*(g.normalized.z 3-g.normalized.z 0))+
      mass 1*(q.delta 3 1^3*(g.normalized.z 3-g.normalized.z 1))=_
    ring
  rw [he]
  obtain ⟨h3,h4,-,-,h0,h1,h2,-,-,-⟩ := g.chart
  simp only [h0,h1,h2,h3,h4] at h ⊢
  field_simp [g.time_ne] at h ⊢
  linear_combination -h

theorem PairGauge.wing_normalization_w :
    2*mass 1*q.delta 0 1^3+mass 2*q.delta 0 2^3-1 =
      g.time^2*(g.coeff 1-mass 2*q.delta 0 2^3*(g.coeff 1-g.coeff 5))-g.time*g.crossW := by
  have h := g.normalized.force_w 0
  change g.normalized.w 0=∑ j, mass j*q.delta 0 j^3*(g.normalized.w 0-g.normalized.w j) at h
  simp [Fin.sum_univ_succ] at h
  have he : g.crossW=mass 3*q.delta 0 3^3*(g.normalized.w 0-g.normalized.w 3)+
      mass 4*q.delta 0 4^3*(g.normalized.w 0-g.normalized.w 4) := by
    change mass 3*(q.delta 0 3^3*(g.normalized.w 0-g.normalized.w 3))+
      mass 4*(q.delta 0 4^3*(g.normalized.w 0-g.normalized.w 4))=_
    ring
  rw [he]
  obtain ⟨-,-,h0,h1,-,-,-,h2,h3,h4⟩ := g.chart
  simp only [h0,h1,h2,h3,h4] at h ⊢
  field_simp [g.time_ne] at h ⊢
  linear_combination -h

theorem inverse_metric (i j : Fin 5) (hij : i≠j) :
    (q.delta i j)⁻¹^2=(g.normalized.z i-g.normalized.z j)*(g.normalized.w i-g.normalized.w j) := by
  have hn : q.delta i j≠0 := by intro h; have hh := q.distance i j hij; simp [h] at hh
  have he := g.normalized.distance i j hij
  change q.delta i j^2*((g.normalized.z i-g.normalized.z j)*(g.normalized.w i-g.normalized.w j))=1 at he
  field_simp [hn]
  linear_combination -he

theorem PairGauge.wing_closure_z :
    (q.delta 3 4)⁻¹^2-2*(q.delta 2 3)⁻¹^2-2*(q.delta 2 4)⁻¹^2 =
      -2*g.time^2*(g.coeff 0-g.coeff 4)*(g.coeff 6+g.coeff 7-2*g.coeff 5) := by
  rw [inverse_metric g 3 4 (by decide),inverse_metric g 2 3 (by decide),inverse_metric g 2 4 (by decide)]
  obtain ⟨h3,h4,-,-,-,-,hz2,hw2,h0,h1⟩ := g.chart
  rw [h3,h4,hz2,hw2,h0,h1]
  field_simp [g.time_ne]
  ring

theorem PairGauge.wing_closure_w :
    (q.delta 0 1)⁻¹^2-2*(q.delta 0 2)⁻¹^2-2*(q.delta 1 2)⁻¹^2 =
      -2*g.time^2*(g.coeff 1-g.coeff 5)*(g.coeff 2+g.coeff 3-2*g.coeff 4) := by
  rw [inverse_metric g 0 1 (by decide),inverse_metric g 0 2 (by decide),inverse_metric g 1 2 (by decide)]
  obtain ⟨-,-,h0,h1,h3,h4,hz2,hw2,-,-⟩ := g.chart
  rw [h0,h1,h3,h4,hz2,hw2]
  field_simp [g.time_ne]
  ring

end
end CentralConfigurations.FiveBody.D6

