import CentralConfigurations.FiveBody.D8.UpperPhase

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology
noncomputable section
variable {mass : Fin 5 → ℂ}

def rootFirst (q : ZWSystem ℂ 5 mass) (U : ℂ) := q.delta 2 4/(q.delta 2 3*U)
def rootSecond (q : ZWSystem ℂ 5 mass) (U : ℂ) := q.delta 3 4/(q.delta 2 3*U)
def rowZ1 (q : ZWSystem ℂ 5 mass) (U : ℂ) := mass 3-(mass 3+upperX q)*rootFirst q U^3
def rowZ2 (q : ZWSystem ℂ 5 mass) (U : ℂ) := -mass 2+(mass 2-upperX q)*rootSecond q U^3
def rowW1 (q : ZWSystem ℂ 5 mass) (U : ℂ) := mass 3-(mass 2+upperY q)*rootFirst q U^3
def rowW2 (q : ZWSystem ℂ 5 mass) (U : ℂ) := -mass 2+(mass 3-upperY q)*rootSecond q U^3
def crossZ (q : ZWSystem ℂ 5 mass) (i : Fin 5) := mass 0*q.zForce i 0+mass 1*q.zForce i 1
def crossW (q : ZWSystem ℂ 5 mass) (i : Fin 5) := mass 0*q.wForce i 0+mass 1*q.wForce i 1

theorem upper_base_metric (q : ZWSystem ℂ 5 mass) (hm : mass 2+mass 3≠0) :
    q.delta 2 3^2*upperS q*upperR q*(mass 2+mass 3)^2=1 := by
  have h := q.distance 2 3 (by decide)
  dsimp [upperS,upperR]
  field_simp [hm]
  linear_combination h

theorem normalized_root_metrics (q : ZWSystem ℂ 5 mass) (U : ℂ)
    (hm : mass 2+mass 3≠0) (hp : mass 2≠0) (hq : mass 3≠0) (hU : U≠0)
    (hshape : U^2*mass 2*mass 3=(mass 2+mass 3)^2) :
    rootFirst q U^2*(1+upperX q/mass 3)*(1+upperY q/mass 2)=1 ∧
    rootSecond q U^2*(1-upperX q/mass 2)*(1-upperY q/mass 3)=1 := by
  have hc := upper_coordinates q hm
  have h24 := q.distance 2 4 (by decide)
  have h34 := q.distance 3 4 (by decide)
  rw [hc.1,hc.2.2.1] at h24
  rw [hc.2.1,hc.2.2.2] at h34
  have hb := upper_base_metric q hm
  have hs := upperS_ne q hm
  have hr := upperR_ne q hm
  constructor
  · dsimp [rootFirst]
    field_simp [q.delta_ne_zero 2 3 (by decide),hU,hp,hq]
    apply (mul_left_cancel₀ (mul_ne_zero hs hr))
    linear_combination h24-hb-q.delta 2 3^2*upperS q*upperR q*hshape
  · dsimp [rootSecond]
    field_simp [q.delta_ne_zero 2 3 (by decide),hU,hp,hq]
    apply (mul_left_cancel₀ (mul_ne_zero hs hr))
    linear_combination h34-hb-q.delta 2 3^2*upperS q*upperR q*hshape

theorem normalized_root_cubes (q : ZWSystem ℂ 5 mass) (U : ℂ) (hU : U≠0)
    (hcu : mass 4*U^3= -(mass 2+mass 3)) :
    mass 4*q.delta 2 4^3= -(mass 2+mass 3)*q.delta 2 3^3*rootFirst q U^3 ∧
    mass 4*q.delta 3 4^3= -(mass 2+mass 3)*q.delta 2 3^3*rootSecond q U^3 := by
  constructor
  · dsimp [rootFirst]
    field_simp [q.delta_ne_zero 2 3 (by decide),hU]
    linear_combination q.delta 2 4^3*hcu
  · dsimp [rootSecond]
    field_simp [q.delta_ne_zero 2 3 (by decide),hU]
    linear_combination q.delta 3 4^3*hcu

theorem upper_force_equations (q : ZWSystem ℂ 5 mass) (U : ℂ)
    (hm : mass 2+mass 3≠0) (hU : U≠0)
    (hcu : mass 4*U^3= -(mass 2+mass 3)) :
    q.z 2=(mass 2+mass 3)*q.delta 2 3^3*upperS q*rowZ1 q U+crossZ q 2 ∧
    q.z 3=(mass 2+mass 3)*q.delta 2 3^3*upperS q*rowZ2 q U+crossZ q 3 ∧
    q.w 2=(mass 2+mass 3)*q.delta 2 3^3*upperR q*rowW1 q U+crossW q 2 ∧
    q.w 3=(mass 2+mass 3)*q.delta 2 3^3*upperR q*rowW2 q U+crossW q 3 := by
  have hc := upper_coordinates q hm
  obtain ⟨hc2,hc3⟩ := normalized_root_cubes q U hU hcu
  have hz2 := q.force_z 2
  have hz3 := q.force_z 3
  have hw2 := q.force_w 2
  have hw3 := q.force_w 3
  simp [Fin.sum_univ_succ,q.delta_diagonal,q.delta_symm 3 2] at hz2 hz3 hw2 hw3
  dsimp [rowZ1,rowZ2,rowW1,rowW2,crossZ,crossW,ZWSystem.zForce,ZWSystem.wForce]
  rw [hc.1,hc.2.1] at hz2 hz3
  rw [hc.2.2.1,hc.2.2.2] at hw2 hw3
  refine ⟨?_,?_,?_,?_⟩
  · rw [hc.1]
    linear_combination hz2+upperS q*(mass 3+upperX q)*hc2
  · rw [hc.2.1]
    linear_combination hz3+upperS q*(upperX q-mass 2)*hc3
  · rw [hc.2.2.1]
    linear_combination hw2+upperR q*(mass 2+upperY q)*hc2
  · rw [hc.2.2.2]
    linear_combination hw3+upperR q*(upperY q-mass 3)*hc3

end
end CentralConfigurations.FiveBody.D8
