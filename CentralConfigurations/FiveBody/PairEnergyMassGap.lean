import CentralConfigurations.FiveBody.PhysicalPotentialFloor
import Mathlib.Tactic

namespace CentralConfigurations.FiveBody.PairEnergy
open scoped BigOperators

theorem binary_gap (p q K J : ℝ) (hp : 0<p) (hq : 0<q) (hK : 0<K) (hJ : 0<J) :
    (p+q+K)*(p*q)^3 < (p+q)*(p*q+(p+q)*K+J)^3 := by
  let P := p+q
  have hP : 0<P := add_pos hp hq
  have hB : 0<3*P^2-p*q := by dsimp [P]; nlinarith [sq_nonneg (p-q)]
  have hrem : 0<K*((p*q)^2*(3*P^2-p*q)+3*P^3*K*(p*q)+P^4*K^2) := by positivity
  have hid : P*(p*q+P*K)^3-(P+K)*(p*q)^3 =
      K*((p*q)^2*(3*P^2-p*q)+3*P^3*K*(p*q)+P^4*K^2) := by ring
  have hbase : (P+K)*(p*q)^3 < P*(p*q+P*K)^3 := by linarith
  have hcube : (p*q+P*K)^3 < (p*q+P*K+J)^3 :=
    (Odd.strictMono_pow (by decide : Odd 3)) (by linarith)
  exact hbase.trans (mul_lt_mul_of_pos_left hcube hP)

theorem physical_scalar_not_binary {m : Fin 5 → ℝ} {I0 : ℝ}
    (hm : ∀ i, 0<m i) (hphysical : PhysicalPotentialLevel m I0)
    (hpair : (m 0+m 1)*I0^3=(m 0*m 1)^3) : False := by
  have hm0 := hm 0; have hm1 := hm 1; have hm2 := hm 2
  have hm3 := hm 3; have hm4 := hm 4
  let K := m 2+m 3+m 4
  let J := m 2*m 3+m 2*m 4+m 3*m 4
  have hK : 0<K := by dsimp [K]; positivity
  have hJ : 0<J := by dsimp [J]; positivity
  have hS : pairMassSum m=m 0*m 1+(m 0+m 1)*K+J := by
    simp [pairMassSum,Fin.sum_univ_succ,K,J]; ring
  have hM : totalMass m=m 0+m 1+K := by simp [totalMass,Fin.sum_univ_succ,K]; ring
  have hg := binary_gap (m 0) (m 1) K J hm0 hm1 hK hJ
  rw [← hS,← hM] at hg
  have hf := mul_le_mul_of_nonneg_left hphysical.2 (le_of_lt (add_pos hm0 hm1))
  have he : (m 0+m 1)*(totalMass m*I0^3)=totalMass m*(m 0*m 1)^3 := by rw [← hpair]; ring
  rw [he] at hf
  linarith

end CentralConfigurations.FiveBody.PairEnergy
