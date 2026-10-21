import CentralConfigurations.FiveBody.PairEnergySupport

namespace CentralConfigurations.FiveBody.PairEnergy
open scoped BigOperators

variable {mass : Fin 5 → ℂ}

def pairMass (mass : Fin 5 → ℂ) := mass 0+mass 1
def tripleMass (mass : Fin 5 → ℂ) := mass 2+mass 3+mass 4
def pairZ (q : ZWSystem ℂ 5 mass) := mass 0*q.z 0+mass 1*q.z 1
def pairW (q : ZWSystem ℂ 5 mass) := mass 0*q.w 0+mass 1*q.w 1
def tripleZ (q : ZWSystem ℂ 5 mass) := mass 2*q.z 2+mass 3*q.z 3+mass 4*q.z 4
def tripleW (q : ZWSystem ℂ 5 mass) := mass 2*q.w 2+mass 3*q.w 3+mass 4*q.w 4
def tripleMetric (q : ZWSystem ℂ 5 mass) :=
  mass 2*mass 3*((q.z 2-q.z 3)*(q.w 2-q.w 3))+
  mass 2*mass 4*((q.z 2-q.z 4)*(q.w 2-q.w 4))+
  mass 3*mass 4*((q.z 3-q.z 4)*(q.w 3-q.w 4))

theorem zw_potential (q : ZWSystem ℂ 5 mass) :
    q.toNormalized.potential = ∑ i, mass i*q.z i*q.w i := by
  rw [q.toNormalized.potential_eq_inertia]
  unfold NormalizedSystem.inertia
  apply Finset.sum_congr rfl
  intro i _
  have h := inverse_zw_separation (q.z i) (q.w i) 0 0
  simp only [add_zero,sub_zero,mul_zero,zero_div] at h
  change mass i*(((q.z i+q.w i)/2)^2+(Complex.I*(q.w i-q.z i)/2)^2)=_
  rw [h]
  ring

theorem tripleZ_eq_neg_pairZ (q : ZWSystem ℂ 5 mass) : tripleZ q = -pairZ q := by
  have h := q.mass_center_z
  simp [Fin.sum_univ_succ] at h
  dsimp [tripleZ,pairZ]
  linear_combination h

theorem tripleW_eq_neg_pairW (q : ZWSystem ℂ 5 mass) : tripleW q = -pairW q := by
  have h := q.mass_center_w
  simp [Fin.sum_univ_succ] at h
  dsimp [tripleW,pairW]
  linear_combination h

/-- Before imposing the total centroid, both exact cluster-center products
appear separately. Their coefficients are the positive cluster masses. -/
theorem two_cluster_inertia (q : ZWSystem ℂ 5 mass) :
    pairMass mass*tripleMass mass*q.toNormalized.potential =
      mass 0*mass 1*tripleMass mass*((q.z 0-q.z 1)*(q.w 0-q.w 1))+
      pairMass mass*tripleMetric q+
      tripleMass mass*pairZ q*pairW q+pairMass mass*tripleZ q*tripleW q := by
  rw [zw_potential]
  simp [Fin.sum_univ_succ,pairMass,tripleMass,tripleMetric,pairZ,pairW,tripleZ,tripleW]
  ring

/-- Full exact inertia decomposition. The internal triple term and the
cluster-center product are retained before taking any limit. -/
theorem full_inertia (q : ZWSystem ℂ 5 mass) :
    pairMass mass*tripleMass mass*q.toNormalized.potential =
      mass 0*mass 1*tripleMass mass*((q.z 0-q.z 1)*(q.w 0-q.w 1))+
      pairMass mass*tripleMetric q+
      (pairMass mass+tripleMass mass)*pairZ q*pairW q := by
  rw [zw_potential]
  have hz := q.mass_center_z
  have hw := q.mass_center_w
  simp [Fin.sum_univ_succ] at hz hw ⊢
  dsimp [pairMass,tripleMass,tripleMetric,pairZ,pairW]
  linear_combination (mass 0+mass 1)*(mass 2*q.w 2+mass 3*q.w 3+mass 4*q.w 4)*hz -
    (mass 0+mass 1)*(mass 0*q.z 0+mass 1*q.z 1)*hw

theorem pairW_boundary (q : ZWSystem ℂ 5 mass) :
    pairW q =
      mass 0*mass 2*q.wForce 0 2 + mass 0*mass 3*q.wForce 0 3 + mass 0*mass 4*q.wForce 0 4 +
      mass 1*mass 2*q.wForce 1 2 + mass 1*mass 3*q.wForce 1 3 + mass 1*mass 4*q.wForce 1 4 := by
  have h := (q.swap.scaledZ 1).boundary_balance {0,1}
  have hc : ({0,1}:Finset (Fin 5))ᶜ = {2,3,4} := by decide
  rw [hc,Finset.sum_product] at h
  simp [ZWSystem.scaledZ,ZWSystem.swap,Finset.sum_insert,Finset.sum_singleton] at h
  dsimp [pairW,ZWSystem.wForce]
  linear_combination h

end CentralConfigurations.FiveBody.PairEnergy
