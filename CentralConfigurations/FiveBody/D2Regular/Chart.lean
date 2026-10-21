import CentralConfigurations.FiveBody.D2Regular.Gauge

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000

abbrev pairIndex (p : Fin 2) : Fin 5 := Fin.natAdd 3 p
abbrev tripleIndex (i : Fin 3) : Fin 5 := i.castLE (by decide)

/-- This chart contains an actual ZW solution and exact normalization identities.
All residual coordinates and all signed roots below are defined from this point. -/
structure ActualChart (m : Fin 5 → ℂ) where
  point : ZWSystem ℂ 5 m
  time : ℂ
  time_ne : time≠0
  pairMass_ne : pairMass m≠0
  tripleMass_ne : tripleMass m≠0
  pair_difference : point.z 4-point.z 3=pairMass m/time
  triangle_extent : point.w 2-tripleCenter m point.w=1/time

def ReciprocalGauge.chart {m : Fin 5 → ℂ} {q : ZWSystem ℂ 5 m}
    (g : ReciprocalGauge q) (hA : pairMass m≠0) (hB : tripleMass m≠0) : ActualChart m :=
  ⟨g.normalized hA,g.time,g.time_ne,hA,hB,g.z_difference hA,g.w_extent hA⟩

namespace ActualChart
variable {m : Fin 5 → ℂ} (s : ActualChart m)

def a (_s : ActualChart m) (p : Fin 2) : ℂ := ![-m 4,m 3] p
def beta : ℂ := (s.point.w 4-s.point.w 3)/(pairMass m*s.time)
def b (p : Fin 2) : ℂ := s.beta*s.a p
def c (i : Fin 3) : ℂ := (s.point.z (tripleIndex i)-tripleCenter m s.point.z)/s.time
def d (i : Fin 3) : ℂ := s.time*(s.point.w (tripleIndex i)-tripleCenter m s.point.w)
def etaZ : ℂ := (tripleCenter m s.point.z-pairCenter m s.point.z)/s.time^2
def etaW : ℂ := (tripleCenter m s.point.w-pairCenter m s.point.w)/s.time^2
def cross (p : Fin 2) (i : Fin 3) : ℂ := s.point.delta (pairIndex p) (tripleIndex i)/s.time
def zeta (p : Fin 2) (i : Fin 3) : ℂ := -s.a p+s.time^2*s.c i+s.time^3*s.etaZ
def chi (p : Fin 2) (i : Fin 3) : ℂ := s.d i-s.time^2*s.b p+s.time^3*s.etaW

theorem a_centered : (∑ p : Fin 2, m (pairIndex p)*s.a p)=0 := by
  simp [a,pairIndex,Fin.sum_univ_succ]; ring

theorem c_centered : (∑ i : Fin 3, m (tripleIndex i)*s.c i)=0 := by
  dsimp [c]
  simp only [Fin.sum_univ_succ]
  dsimp [tripleIndex,tripleCenter]
  field_simp [s.time_ne,s.tripleMass_ne]
  dsimp [tripleMass]; ring

theorem d_centered : (∑ i : Fin 3, m (tripleIndex i)*s.d i)=0 := by
  dsimp [d]
  simp only [Fin.sum_univ_succ]
  dsimp [tripleIndex,tripleCenter]
  field_simp [s.tripleMass_ne]
  dsimp [tripleMass]; ring

theorem d_last : s.d 2=1 := by
  dsimp [d,tripleIndex]
  rw [s.triangle_extent]
  field_simp [s.time_ne]

theorem pair_z (p : Fin 2) :
    s.point.z (pairIndex p)=pairCenter m s.point.z+s.a p/s.time := by
  have hh := s.pair_difference
  field_simp [s.time_ne] at hh
  fin_cases p <;> dsimp [a,pairIndex,pairCenter]
  all_goals field_simp [s.pairMass_ne,s.time_ne]
  all_goals dsimp [pairMass] at hh ⊢
  · linear_combination -m 4*hh
  · linear_combination m 3*hh

theorem pair_w (p : Fin 2) :
    s.point.w (pairIndex p)=pairCenter m s.point.w+s.time*s.b p := by
  fin_cases p <;> dsimp [b,beta,a,pairIndex,pairCenter]
  all_goals field_simp [s.pairMass_ne,s.time_ne]
  all_goals dsimp [pairMass]; ring

theorem triple_z (i : Fin 3) :
    s.point.z (tripleIndex i)=tripleCenter m s.point.z+s.time*s.c i := by
  dsimp [c]; field_simp [s.time_ne]; ring

theorem triple_w (i : Fin 3) :
    s.point.w (tripleIndex i)=tripleCenter m s.point.w+s.d i/s.time := by
  dsimp [d]; field_simp [s.time_ne]; ring

theorem zeta_eq (p : Fin 2) (i : Fin 3) :
    s.zeta p i=s.time*(s.point.z (tripleIndex i)-s.point.z (pairIndex p)) := by
  rw [s.pair_z p]
  dsimp [zeta,c,etaZ]
  field_simp [s.time_ne]
  ring

theorem chi_eq (p : Fin 2) (i : Fin 3) :
    s.chi p i=s.time*(s.point.w (tripleIndex i)-s.point.w (pairIndex p)) := by
  rw [s.pair_w p]
  dsimp [chi,d,etaW]
  field_simp [s.time_ne]
  ring

theorem cross_metric (p : Fin 2) (i : Fin 3) :
    s.cross p i^2*s.zeta p i*s.chi p i=1 := by
  rw [s.zeta_eq,s.chi_eq]
  have hd := s.point.distance (pairIndex p) (tripleIndex i)
    (by fin_cases p <;> fin_cases i <;> decide)
  dsimp [cross]
  field_simp [s.time_ne]
  linear_combination hd

theorem internal_metric (i j : Fin 3) (hij : i≠j) :
    s.point.delta (tripleIndex i) (tripleIndex j)^2*((s.c i-s.c j)*(s.d i-s.d j))=1 := by
  have hh : tripleIndex i≠tripleIndex j := by
    exact fun h => hij (Fin.ext (congrArg (fun x : Fin 5 => x.val) h))
  have hd := s.point.distance (tripleIndex i) (tripleIndex j) hh
  dsimp [c,d]
  field_simp [s.time_ne]
  linear_combination hd

end ActualChart
end
end CentralConfigurations.FiveBody.D2.Regular
