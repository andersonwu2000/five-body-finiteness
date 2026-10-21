import CentralConfigurations.FiveBody.D2Actual.PhysicalExtraction
import CentralConfigurations.Model.FixedPotentialLevel
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

def pairMass (m : Fin 5 → ℂ) : ℂ := m 3 + m 4
def tripleMass (m : Fin 5 → ℂ) : ℂ := m 0 + m 1 + m 2
def pairCenter (m v : Fin 5 → ℂ) : ℂ := (m 3*v 3+m 4*v 4)/pairMass m
def tripleCenter (m v : Fin 5 → ℂ) : ℂ :=
  (m 0*v 0+m 1*v 1+m 2*v 2)/tripleMass m

theorem tripleCenter_smul (m v : Fin 5 → ℂ) (a : ℂ) :
    tripleCenter m (fun i => a*v i)=a*tripleCenter m v := by
  unfold tripleCenter; ring

/-- The exact source chart gauge on an actual point; no asymptotic field. -/
structure ReciprocalGauge {m : Fin 5 → ℂ} (q : ZWSystem ℂ 5 m) where
  time : ℂ
  time_ne : time≠0
  time_square : time^2=pairMass m/((q.z 4-q.z 3)*(q.w 2-tripleCenter m q.w))

def reciprocalGauge {m : Fin 5 → ℂ} (q : ZWSystem ℂ 5 m)
    (hA : pairMass m≠0) (hE : q.w 2-tripleCenter m q.w≠0) : ReciprocalGauge q := by
  let hr := IsAlgClosed.exists_pow_nat_eq
    (pairMass m/((q.z 4-q.z 3)*(q.w 2-tripleCenter m q.w))) (by decide : 0<2)
  let h := Classical.choose hr
  have hh := Classical.choose_spec hr
  refine ⟨h,?_,hh⟩
  intro hz
  have hn := div_ne_zero hA (mul_ne_zero (q.z_separation_ne_zero (by decide : (4:Fin 5)≠3)) hE)
  apply hn
  rw [← hh]
  change h^2=0
  rw [hz]
  norm_num

namespace ReciprocalGauge
variable {m : Fin 5 → ℂ} {q : ZWSystem ℂ 5 m} (g : ReciprocalGauge q)

def rotation : ℂ := g.time*(q.w 2-tripleCenter m q.w)

include g in
theorem extent_ne (_hA : pairMass m≠0) : q.w 2-tripleCenter m q.w≠0 := by
  intro hz
  have hh := g.time_square
  simp [hz] at hh
  exact g.time_ne hh

theorem rotation_ne (hA : pairMass m≠0) : g.rotation≠0 :=
  mul_ne_zero g.time_ne (g.extent_ne hA)

def normalized (hA : pairMass m≠0) : ZWSystem ℂ 5 m :=
  q.rescale g.rotation (g.rotation_ne hA)

theorem z_difference (hA : pairMass m≠0) :
    (g.normalized hA).z 4-(g.normalized hA).z 3=pairMass m/g.time := by
  have hh := g.time_square
  have hD := q.z_separation_ne_zero (by decide : (4:Fin 5)≠3)
  have hE := g.extent_ne hA
  field_simp [hD,hE] at hh
  dsimp [normalized,ZWSystem.rescale,rotation]
  field_simp [g.time_ne]
  linear_combination hh

theorem w_extent (hA : pairMass m≠0) :
    (g.normalized hA).w 2-tripleCenter m (g.normalized hA).w=1/g.time := by
  change g.rotation⁻¹*q.w 2-tripleCenter m (fun i => g.rotation⁻¹*q.w i)=_
  rw [tripleCenter_smul]
  dsimp [rotation]
  field_simp [g.time_ne,g.extent_ne hA]

theorem potential (hA : pairMass m≠0) :
    (g.normalized hA).toNormalized.potential=q.toNormalized.potential := rfl

end ReciprocalGauge
end
end CentralConfigurations.FiveBody.D2.Regular
