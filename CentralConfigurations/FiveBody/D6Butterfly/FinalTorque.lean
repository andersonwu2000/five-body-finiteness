import CentralConfigurations.FiveBody.D6Butterfly.ZeroLimits

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

theorem zero_first_order_bigO {f t : ℕ → ℂ} {D : ℂ}
    (ht : Tendsto t atTop (𝓝 0))
    (hf : (fun n => f n-t n*D) =O[atTop] (fun n => t n^2)) : f =O[atTop] t := by
  have ht2 : (fun n => t n^2) =O[atTop] t := by
    simpa only [pow_two] using order_mul_bounded (isBigO_refl t atTop) (ht.isBigO_one ℂ)
  exact ((hf.trans ht2).add ((isBigO_refl t atTop).const_mul_left D)).congr_left (fun n => by ring)

theorem zero_product_second_order {f g t : ℕ → ℂ} {D E : ℂ}
    (ht : Tendsto t atTop (𝓝 0))
    (hf : (fun n => f n-t n*D) =O[atTop] (fun n => t n^2))
    (hg : (fun n => g n-t n*E) =O[atTop] (fun n => t n^2)) :
    (fun n => f n*g n-t n^2*(D*E)) =O[atTop] (fun n => t n^3) := by
  have hgb := zero_first_order_bigO ht hg
  have h1 : (fun n => (f n-t n*D)*g n) =O[atTop] (fun n => t n^3) := by
    simpa only [pow_succ] using hf.mul hgb
  have h2 : (fun n => D*(t n*(g n-t n*E))) =O[atTop] (fun n => t n^3) := by
    simpa only [← pow_succ'] using ((isBigO_refl t atTop).mul hg).const_mul_left D
  exact (h1.add h2).congr_left (fun n => by ring)

theorem final_torque_coefficient {v : ℕ → Fin 8 → ℂ} {t A B : ℕ → ℂ}
    {c : Fin 8 → ℂ} {a b d H K : ℂ}
    (ht : Tendsto t atTop (𝓝 0)) (htn : ∀ n, t n≠0)
    (hj : ∀ i, (fun n => v n i-c i-t n*driftVector a b d H K i) =O[atTop] (fun n => t n^2))
    (hp0 : c 4=0) (hq0 : c 5=0) (hC0 : torqueCoefficient c H K=0)
    (hA : A =O[atTop] (fun n => t n^2)) (hB : B =O[atTop] (fun n => t n^2))
    (hJ : (fun n => reducedExpression a b d (v n) (A n) (B n) (t n) H K) =O[atTop] (fun n => t n^3)) :
    d*(driftD b H K*driftE a H K)-a*b*torqueCoefficient (driftVector a b d H K) H K=0 := by
  have hp : (fun n => v n 4-t n*driftE a H K) =O[atTop] (fun n => t n^2) := by simpa only [hp0,sub_zero] using hj 4
  have hq : (fun n => v n 5-t n*driftD b H K) =O[atTop] (fun n => t n^2) := by simpa only [hq0,sub_zero] using hj 5
  have hpq := zero_product_second_order ht hq hp
  have hqB : (fun n => v n 5*B n) =O[atTop] (fun n => t n^3) := by
    simpa only [← pow_succ'] using (zero_first_order_bigO ht hq).mul hB
  have hpA : (fun n => v n 4*A n) =O[atTop] (fun n => t n^3) := by
    simpa only [← pow_succ'] using (zero_first_order_bigO ht hp).mul hA
  have hC := torque_coefficient_order H K hj
  have hTC : (fun n => t n*torqueCoefficient (v n) H K-t n^2*torqueCoefficient (driftVector a b d H K) H K) =O[atTop]
      (fun n => t n^3) := by
    have hh := (isBigO_refl t atTop).mul hC
    have hr : (fun n => t n*(torqueCoefficient (v n) H K-torqueCoefficient c H K-
      t n*torqueCoefficient (driftVector a b d H K) H K)) =O[atTop] (fun n => t n^3) := by
      simpa only [← pow_succ'] using hh
    exact hr.congr_left (fun n => by rw [hC0]; ring)
  have hR := (((hpq.sub hqB).sub hpA).const_mul_left d).sub (hTC.const_mul_left (a*b))
  apply coefficient_zero ht htn 2
  apply (hJ.sub hR).congr_left
  intro n
  dsimp [reducedExpression]
  ring

theorem final_coefficient_nonzero {a b d : ℝ} (ha : 0<a) (hb : 0<b) (hd : 0<d)
    {H K : ℂ} (hH : H^2= -1) (hK : K^2=1) :
    (d:ℂ)*(driftD b H K*driftE a H K)-(a:ℂ)*b*torqueCoefficient (driftVector a b d H K) H K≠0 := by
  have han : (a:ℂ)≠0 := by exact_mod_cast ne_of_gt ha
  have hbn : (b:ℂ)≠0 := by exact_mod_cast ne_of_gt hb
  have hH6 : H^6= -1 := by rw [show 6=2*3 from rfl,pow_mul,hH]; norm_num
  have hK6 : K^6=1 := by rw [show 6=2*3 from rfl,pow_mul,hK]; norm_num
  have he : (d:ℂ)*(driftD b H K*driftE a H K)-(a:ℂ)*b*torqueCoefficient (driftVector a b d H K) H K=
      -4*(a:ℂ)*b*(2*a+2*b+d) := by
    calc
      _ = 2*(a:ℂ)*b*(2*a+2*b+d)*(H^6-K^6) := by
        dsimp [driftD,driftE,torqueCoefficient,driftVector]
        field_simp [han,hbn]
        ring
      _ = _ := by rw [hH6,hK6]; ring
  rw [he]
  have hM : (2*(a:ℂ)+2*b+d)≠0 := by
    have h : 0<2*a+2*b+d := by positivity
    exact_mod_cast ne_of_gt h
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) han) hbn) hM

end CentralConfigurations.FiveBody.D6
