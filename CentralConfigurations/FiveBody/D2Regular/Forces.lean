import CentralConfigurations.FiveBody.D2Regular.Centers

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000

namespace ActualChart
variable {m : Fin 5 → ℂ} (s : ActualChart m)

def meanT (_s : ActualChart m) (v : Fin 3 → ℂ) : ℂ := (∑ i, m (tripleIndex i)*v i)/tripleMass m
def meanP (_s : ActualChart m) (v : Fin 2 → ℂ) : ℂ := (∑ p, m (pairIndex p)*v p)/pairMass m
def Hz (i : Fin 3) : ℂ := ∑ p : Fin 2, m (pairIndex p)*s.cross p i^3*s.zeta p i
def Hw (i : Fin 3) : ℂ := ∑ p : Fin 2, m (pairIndex p)*s.cross p i^3*s.chi p i
def Gz (p : Fin 2) : ℂ := ∑ i : Fin 3, m (tripleIndex i)*s.cross p i^3*s.zeta p i
def Gw (p : Fin 2) : ℂ := ∑ i : Fin 3, m (tripleIndex i)*s.cross p i^3*s.chi p i
def Fz (i : Fin 3) : ℂ := s.c i-∑ j : Fin 3,
  m (tripleIndex j)*s.point.delta (tripleIndex i) (tripleIndex j)^3*(s.c i-s.c j)
def Fw (i : Fin 3) : ℂ := s.d i-∑ j : Fin 3,
  m (tripleIndex j)*s.point.delta (tripleIndex i) (tripleIndex j)^3*(s.d i-s.d j)

theorem Hz_mean : s.meanT s.Hz=s.crossSumZ/tripleMass m := by
  dsimp [meanT,Hz,crossSumZ]
  congr 1
  rw [Finset.sum_comm]
  simp only [Fin.sum_univ_succ]
  ring

theorem Hw_mean : s.meanT s.Hw=s.crossSumW/tripleMass m := by
  dsimp [meanT,Hw,crossSumW]
  congr 1
  rw [Finset.sum_comm]
  simp only [Fin.sum_univ_succ]
  ring

theorem Gz_mean : s.meanP s.Gz=s.crossSumZ/pairMass m := by
  dsimp [meanP,Gz,crossSumZ]
  simp only [Fin.sum_univ_succ]
  ring

theorem Gw_mean : s.meanP s.Gw=s.crossSumW/pairMass m := by
  dsimp [meanP,Gw,crossSumW]
  simp only [Fin.sum_univ_succ]
  ring

theorem cross_z_force (p : Fin 2) (i : Fin 3) :
    s.point.delta (pairIndex p) (tripleIndex i)^3*
      (s.point.z (tripleIndex i)-s.point.z (pairIndex p))=
      s.time^2*s.cross p i^3*s.zeta p i := by
  rw [s.zeta_eq]
  dsimp [cross]
  field_simp [s.time_ne]

theorem cross_w_force (p : Fin 2) (i : Fin 3) :
    s.point.delta (pairIndex p) (tripleIndex i)^3*
      (s.point.w (tripleIndex i)-s.point.w (pairIndex p))=
      s.time^2*s.cross p i^3*s.chi p i := by
  rw [s.chi_eq]
  dsimp [cross]
  field_simp [s.time_ne]

theorem triangle_z_residual (i : Fin 3) : s.Fz i=s.time*(s.Hz i-s.meanT s.Hz) := by
  have hf := s.point.force_z (tripleIndex i)
  have hs : s.point.z (tripleIndex i)=
      (∑ j : Fin 3, m (tripleIndex j)*s.point.delta (tripleIndex i) (tripleIndex j)^3*
        (s.point.z (tripleIndex i)-s.point.z (tripleIndex j)))+
      (∑ p : Fin 2, m (pairIndex p)*s.point.delta (pairIndex p) (tripleIndex i)^3*
        (s.point.z (tripleIndex i)-s.point.z (pairIndex p))) := by
    simpa [Fin.sum_univ_succ,pairIndex,tripleIndex,add_assoc,
      s.point.delta_symm (Fin.castLE (by decide) i) 3,
      s.point.delta_symm (Fin.castLE (by decide) i) 4] using hf
  have hd (j : Fin 3) : s.point.z (tripleIndex i)-s.point.z (tripleIndex j)=
      s.time*(s.c i-s.c j) := by
    dsimp [c]; field_simp [s.time_ne]; ring
  simp_rw [mul_assoc (m _),s.cross_z_force] at hs
  simp_rw [hd] at hs
  rw [s.triple_z i,s.triple_center_z] at hs
  rw [s.Hz_mean]
  dsimp [Fz,Hz]
  simp [Fin.sum_univ_succ] at hs ⊢
  apply (mul_left_cancel₀ s.time_ne)
  field_simp [s.time_ne,s.tripleMass_ne] at hs ⊢
  linear_combination hs

theorem triangle_w_residual (i : Fin 3) : s.Fw i=s.time^3*(s.Hw i-s.meanT s.Hw) := by
  have hf := s.point.force_w (tripleIndex i)
  have hs : s.point.w (tripleIndex i)=
      (∑ j : Fin 3, m (tripleIndex j)*s.point.delta (tripleIndex i) (tripleIndex j)^3*
        (s.point.w (tripleIndex i)-s.point.w (tripleIndex j)))+
      (∑ p : Fin 2, m (pairIndex p)*s.point.delta (pairIndex p) (tripleIndex i)^3*
        (s.point.w (tripleIndex i)-s.point.w (pairIndex p))) := by
    simpa [Fin.sum_univ_succ,pairIndex,tripleIndex,add_assoc,
      s.point.delta_symm (Fin.castLE (by decide) i) 3,
      s.point.delta_symm (Fin.castLE (by decide) i) 4] using hf
  have hd (j : Fin 3) : s.point.w (tripleIndex i)-s.point.w (tripleIndex j)=
      (s.d i-s.d j)/s.time := by
    dsimp [d]; field_simp [s.time_ne]; ring
  simp_rw [mul_assoc (m _),s.cross_w_force] at hs
  simp_rw [hd] at hs
  rw [s.triple_w i,s.triple_center_w] at hs
  rw [s.Hw_mean]
  dsimp [Fw,Hw]
  simp [Fin.sum_univ_succ] at hs ⊢
  field_simp [s.time_ne,s.tripleMass_ne] at hs ⊢
  linear_combination hs

end ActualChart
end
end CentralConfigurations.FiveBody.D2.Regular
