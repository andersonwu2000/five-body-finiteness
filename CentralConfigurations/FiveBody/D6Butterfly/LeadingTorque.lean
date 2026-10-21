import CentralConfigurations.FiveBody.D6Butterfly.TorqueOrders

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology
noncomputable section

theorem constant_error_tendsto {f ε : ℕ → ℂ} {c : ℂ}
    (h : (fun t => f t-c) =O[atTop] ε) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 c) := by
  simpa only [zero_add] using ((h.trans_tendsto hε).add_const c).congr (fun t => by ring)

def reducedExpression (a b d : ℂ) (v : Fin 8 → ℂ) (A B t H K : ℂ) : ℂ :=
  d*(v 5*v 4-v 5*B-v 4*A)-a*b*t*torqueCoefficient v H K
def firstTorqueCoefficient (a b d : ℂ) (c : Fin 8 → ℂ) (x y H K : ℂ) : ℂ :=
  d*(driftD b H K*c 4+driftE a H K*c 5-driftD b H K*y*c 4-driftE a H K*x*c 5)-
    a*b*torqueCoefficient c H K

theorem leading_torque_coefficients {v : ℕ → Fin 8 → ℂ} {t A B : ℕ → ℂ}
    {c : Fin 8 → ℂ} {a b d x y H K : ℂ}
    (ht : Tendsto t atTop (𝓝 0)) (htn : ∀ n, t n≠0)
    (hv : ∀ i, Tendsto (fun n => v n i) atTop (𝓝 (c i)))
    (hj : ∀ i, (fun n => v n i-c i-t n*driftVector a b d H K i) =O[atTop] (fun n => t n^2))
    (hA : (fun n => A n-x*c 5) =O[atTop] (fun n => t n^2))
    (hB : (fun n => B n-y*c 4) =O[atTop] (fun n => t n^2))
    (hJ : (fun n => reducedExpression a b d (v n) (A n) (B n) (t n) H K) =O[atTop] (fun n => t n^3)) :
    d*c 4*c 5*(1-x-y)=0 ∧ firstTorqueCoefficient a b d c x y H K=0 := by
  have ht2 : Tendsto (fun n => t n^2) atTop (𝓝 0) := by simpa using ht.pow 2
  have hAlim := constant_error_tendsto hA ht2
  have hBlim := constant_error_tendsto hB ht2
  have hp : (fun n => v n 4-c 4-t n*driftE a H K) =O[atTop] (fun n => t n^2) := hj 4
  have hq : (fun n => v n 5-c 5-t n*driftD b H K) =O[atTop] (fun n => t n^2) := hj 5
  have hA0 : (fun n => A n-x*c 5-t n*0) =O[atTop] (fun n => t n^2) := by simpa using hA
  have hB0 : (fun n => B n-y*c 4-t n*0) =O[atTop] (fun n => t n^2) := by simpa using hB
  have hpq := product_first_order ht ((hv 4).isBigO_one ℂ) hq hp
  have hqB := product_first_order ht (hBlim.isBigO_one ℂ) hq hB0
  have hpA := product_first_order ht (hAlim.isBigO_one ℂ) hp hA0
  have hC := torque_coefficient_order H K hj
  have hTC : (fun n => t n*torqueCoefficient (v n) H K-t n*torqueCoefficient c H K) =O[atTop] (fun n => t n^2) := by
    apply ((order_mul_bounded hC (ht.isBigO_one ℂ)).add
      ((isBigO_refl (fun n => t n^2) atTop).const_mul_left (torqueCoefficient (driftVector a b d H K) H K))).congr_left
    intro n
    ring
  have hjet : (fun n => reducedExpression a b d (v n) (A n) (B n) (t n) H K-
      d*c 4*c 5*(1-x-y)-t n*firstTorqueCoefficient a b d c x y H K) =O[atTop] (fun n => t n^2) := by
    apply ((((hpq.sub hqB).sub hpA).const_mul_left d).sub (hTC.const_mul_left (a*b))).congr_left
    intro n
    dsimp [reducedExpression,firstTorqueCoefficient]
    ring
  exact first_coefficients_zero ht htn hJ hjet

theorem cross_cube_sums_ne {H K : ℂ} (hH : H^2= -1) (hK : K^2=1) :
    H^3+K^3≠0 ∧ H^3-K^3≠0 := by
  have hH3 : H^3= -H := by rw [show 3=2+1 from rfl,pow_succ,hH]; ring
  have hK3 : K^3=K := by rw [show 3=2+1 from rfl,pow_succ,hK,one_mul]
  constructor <;> intro h
  · rw [hH3,hK3] at h
    have he : H=K := by linear_combination -h
    rw [he,hK] at hH
    norm_num at hH
  · rw [hH3,hK3] at h
    have he : H= -K := by linear_combination -h
    rw [he] at hH
    norm_num [hK] at hH

end
end CentralConfigurations.FiveBody.D6
