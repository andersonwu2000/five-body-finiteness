import CentralConfigurations.FiveBody.D2EllZero.QuadraticParts
import CentralConfigurations.FiveBody.D2Exceptional.EllZeroActual
import CentralConfigurations.Model.ZWMassCenter

namespace CentralConfigurations.FiveBody.D2.EllZero
open Exceptional
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem centered0 {w0 w1 w2 g x : ℂ} (hk : RankK0 x=0)
    (h01 : w1-w0=g) (h02 : w2-w0=g*x) (hc : w0+5*w1+w2=0) :
    ‖w0‖^2=‖w2‖^2 ∧ 8*‖w1‖^2=‖w0‖^2 := by
  have he0 : w0= -g*(5+x)/7 := by linear_combination (1/7 : ℂ)*hc-(5/7 : ℂ)*h01-(1/7 : ℂ)*h02
  have he1 : w1= g*(2-x)/7 := by linear_combination he0+h01
  have he2 : w2= g*(6*x-5)/7 := by linear_combination he0+h02
  obtain ⟨hr,hi⟩ := rank0_parts hk
  have h0 : Complex.normSq (5+x)=28 := by
    norm_num [Complex.normSq_apply,hr]; nlinarith
  have h1 : Complex.normSq (2-x)=7/2 := by
    norm_num [Complex.normSq_apply,hr]; nlinarith
  have h2 : Complex.normSq (6*x-5)=28 := by
    norm_num [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,hr]; nlinarith
  simp only [← Complex.normSq_eq_norm_sq]
  rw [he0,he1,he2]
  simp only [Complex.normSq_div,Complex.normSq_mul,Complex.normSq_neg,h0,h1,h2]
  norm_num [Complex.normSq_apply]
  ring

theorem centered1 {w0 w1 w2 g x : ℂ} (hk : RankK1 x=0)
    (h01 : w1-w0=g) (h02 : w2-w0=g*x) (hc : w0+w1+5*w2=0) :
    ‖w0‖^2=‖w1‖^2 ∧ 8*‖w2‖^2=‖w0‖^2 := by
  have he0 : w0= -g*(1+5*x)/7 := by linear_combination (1/7 : ℂ)*hc-(1/7 : ℂ)*h01-(5/7 : ℂ)*h02
  have he1 : w1= g*(6-5*x)/7 := by linear_combination he0+h01
  have he2 : w2= g*(2*x-1)/7 := by linear_combination he0+h02
  obtain ⟨hr,hi⟩ := rank1_parts hk
  have h0 : Complex.normSq (1+5*x)=56 := by
    norm_num [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,hr]; nlinarith
  have h1 : Complex.normSq (6-5*x)=56 := by
    norm_num [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,hr]; nlinarith
  have h2 : Complex.normSq (2*x-1)=7 := by
    norm_num [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,hr]; nlinarith
  simp only [← Complex.normSq_eq_norm_sq]
  rw [he0,he1,he2]
  simp only [Complex.normSq_div,Complex.normSq_mul,Complex.normSq_neg,h0,h1,h2]
  norm_num [Complex.normSq_apply]
  ring

theorem centered3 {w0 w1 w2 g x : ℂ} (hk : RankK3 x=0)
    (h01 : w1-w0=g) (h02 : w2-w0=g*x) (hc : 5*w0+w1+w2=0) :
    ‖w1‖^2=‖w2‖^2 ∧ 8*‖w0‖^2=‖w1‖^2 := by
  have he0 : w0= -g*(1+x)/7 := by linear_combination (1/7 : ℂ)*hc-(1/7 : ℂ)*h01-(1/7 : ℂ)*h02
  have he1 : w1= g*(6-x)/7 := by linear_combination he0+h01
  have he2 : w2= g*(6*x-1)/7 := by linear_combination he0+h02
  obtain ⟨hr,hi⟩ := rank3_parts hk
  have h0 : Complex.normSq (1+x)=7/2 := by
    norm_num [Complex.normSq_apply,hr]; nlinarith
  have h1 : Complex.normSq (6-x)=28 := by
    norm_num [Complex.normSq_apply,hr]; nlinarith
  have h2 : Complex.normSq (6*x-1)=28 := by
    norm_num [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,hr]; nlinarith
  simp only [← Complex.normSq_eq_norm_sq]
  rw [he0,he1,he2]
  simp only [Complex.normSq_div,Complex.normSq_mul,Complex.normSq_neg,h0,h1,h2]
  norm_num [Complex.normSq_apply]
  ring

end CentralConfigurations.FiveBody.D2.EllZero
