import CentralConfigurations.FiveBody.D2Exceptional.EllZeroActual

namespace CentralConfigurations.FiveBody.D2.EllZero

def role0 : Fin 3 ≃ Fin 3 where
  toFun := ![0,1,2]
  invFun := ![0,1,2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def role1 : Fin 3 ≃ Fin 3 where
  toFun := ![0,2,1]
  invFun := ![0,2,1]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def role3 : Fin 3 ≃ Fin 3 where
  toFun := ![1,0,2]
  invFun := ![1,0,2]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def fullRole0 : Fin 5 ≃ Fin 5 where
  toFun := ![0,1,2,3,4]
  invFun := ![0,1,2,3,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def fullRole1 : Fin 5 ≃ Fin 5 where
  toFun := ![0,2,1,3,4]
  invFun := ![0,2,1,3,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def fullRole3 : Fin 5 ≃ Fin 5 where
  toFun := ![1,0,2,3,4]
  invFun := ![1,0,2,3,4]
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

theorem full_role0_triangle (i : Fin 3) :
    fullRole0 (i.castLE (by decide)) = (role0 i).castLE (by decide) := by
  fin_cases i <;> rfl

theorem full_role1_triangle (i : Fin 3) :
    fullRole1 (i.castLE (by decide)) = (role1 i).castLE (by decide) := by
  fin_cases i <;> rfl

theorem full_role3_triangle (i : Fin 3) :
    fullRole3 (i.castLE (by decide)) = (role3 i).castLE (by decide) := by
  fin_cases i <;> rfl

theorem full_roles_fix_pair (p : Fin 2) :
    fullRole0 (Fin.natAdd 3 p)=Fin.natAdd 3 p ∧
    fullRole1 (Fin.natAdd 3 p)=Fin.natAdd 3 p ∧
    fullRole3 (Fin.natAdd 3 p)=Fin.natAdd 3 p := by
  fin_cases p <;> exact ⟨rfl,rfl,rfl⟩

end CentralConfigurations.FiveBody.D2.EllZero
