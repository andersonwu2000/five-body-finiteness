import CentralConfigurations.FiveBody.D2Regular.PairForces

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000

namespace ActualChart
variable {m : Fin 5 → ℂ} (s : ActualChart m)

theorem pair_centered_torque (p : Fin 2) :
    s.a p*(s.Gw p-s.meanP s.Gw)-s.time^2*s.b p*(s.Gz p-s.meanP s.Gz)=0 := by
  have hz := s.pair_z_residual p
  have hw := s.pair_w_residual p
  apply (mul_left_cancel₀ s.time_ne)
  linear_combination s.a p*hw-s.b p*hz

/-- The original pair torque, derived from the original force rows after the
exact gauge; no ordinary torque is introduced as an extra equation. -/
theorem pair_torque :
    (∑ p : Fin 2, ∑ i : Fin 3,
      m (pairIndex p)*m (tripleIndex i)*s.cross p i^3*
        (s.a p*s.chi p i-s.time^2*s.b p*s.zeta p i))=0 := by
  have h0 := s.pair_centered_torque 0
  have h1 := s.pair_centered_torque 1
  simp [meanP,Gw,Gz,a,b,Fin.sum_univ_succ,pairIndex,tripleIndex] at h0 h1 ⊢
  linear_combination m 3*h0+m 4*h1

def unsquaredTorque : ℂ := ∑ p : Fin 2, ∑ i : Fin 3,
  m (pairIndex p)*m (tripleIndex i)*s.cross p i

def torqueRemainder : ℂ := ∑ p : Fin 2, ∑ i : Fin 3,
  m (pairIndex p)*m (tripleIndex i)*s.cross p i^3*
    (s.c i*s.chi p i-s.b p*s.zeta p i)

/-- Full finite-chart equation whose constant and first coefficients are the
old unsquared W and the additional response scalar. The center term remains. -/
theorem unsquared_torque_equation :
    s.unsquaredTorque=s.time^2*s.torqueRemainder+s.time^3*s.etaZ*s.crossSumW := by
  have he (p : Fin 2) (i : Fin 3) :
      s.cross p i^3*(s.a p*s.chi p i-s.time^2*s.b p*s.zeta p i)=
      -s.cross p i+s.time^2*s.cross p i^3*(s.c i*s.chi p i-s.b p*s.zeta p i)+
        s.time^3*s.etaZ*s.cross p i^3*s.chi p i := by
    have hm := s.cross_metric p i
    have hz : s.a p= -s.zeta p i+s.time^2*s.c i+s.time^3*s.etaZ := by
      dsimp [zeta]; ring
    rw [hz]
    linear_combination -s.cross p i*hm
  have hh := s.pair_torque
  simp_rw [mul_assoc (m _),he] at hh
  dsimp [unsquaredTorque,torqueRemainder,crossSumW]
  simp [Fin.sum_univ_succ] at hh ⊢
  linear_combination -hh

/-- Exact edgewise redundancy of the two internal rotational brackets. -/
theorem torque_bracket_identity (p : Fin 2) (i : Fin 3) :
    (s.a p*s.chi p i-s.time^2*s.b p*s.zeta p i)+
      (s.d i*s.zeta p i-s.time^2*s.c i*s.chi p i)=
      s.time^3*(s.etaZ*s.chi p i-s.etaW*s.zeta p i) := by
  dsimp [zeta,chi]
  ring

end ActualChart
end
end CentralConfigurations.FiveBody.D2.Regular
