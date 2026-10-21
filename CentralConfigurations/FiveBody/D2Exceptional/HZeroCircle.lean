import CentralConfigurations.FiveBody.D2Exceptional.HZeroBezout
import Mathlib.Analysis.Complex.Basic

namespace CentralConfigurations.FiveBody.D2.Exceptional
set_option maxHeartbeats 1000000

theorem star_of_square_neg_three {h : ℂ} (hh : h^2+3=0) : star h = -h := by
  have hre := congrArg Complex.re hh
  have him := congrArg Complex.im hh
  simp [pow_two,Complex.mul_re,Complex.mul_im] at hre him
  have him0 : h.im ≠ 0 := by intro he; rw [he] at hre; nlinarith [sq_nonneg h.re]
  have hre0 : h.re = 0 := by
    have he : h.re*h.im = 0 := by nlinarith
    exact (mul_eq_zero.mp he).resolve_right him0
  apply Complex.ext <;> simp [hre0]

theorem star_eq_inverse_of_norm_one {y : ℂ} (hy : ‖y‖=1) : star y=y⁻¹ := by
  have hy0 : y ≠ 0 := by intro he; simp [he] at hy
  apply mul_left_cancel₀ hy0
  rw [mul_inv_cancel₀ hy0]
  simpa [Complex.star_def,hy] using Complex.mul_conj' y

theorem reciprocal0 {h y : ℂ} (hh : h^2+3=0) (hy : ‖y‖=1) :
    Pc0 h y = y^5*star (P0 h y) := by
  have hy0 : y ≠ 0 := by intro he; simp [he] at hy
  simp [P0,Pc0,star_of_square_neg_three hh,star_eq_inverse_of_norm_one hy]
  field_simp
  ring

theorem reciprocal1 {h y : ℂ} (hh : h^2+3=0) (hy : ‖y‖=1) :
    Pc1 h y = y^5*star (P1 h y) := by
  have hy0 : y ≠ 0 := by intro he; simp [he] at hy
  simp [P1,Pc1,star_of_square_neg_three hh,star_eq_inverse_of_norm_one hy]
  field_simp
  ring

theorem reciprocal2 {h y : ℂ} (hh : h^2+3=0) (hy : ‖y‖=1) :
    Pc2 h y = y^5*star (P2 h y) := by
  have hy0 : y ≠ 0 := by intro he; simp [he] at hy
  simp [P2,Pc2,star_of_square_neg_three hh,star_eq_inverse_of_norm_one hy]
  field_simp
  ring

theorem reciprocal3 {h y : ℂ} (hh : h^2+3=0) (hy : ‖y‖=1) :
    Pc3 h y = y^5*star (P3 h y) := by
  have hy0 : y ≠ 0 := by intro he; simp [he] at hy
  simp [P3,Pc3,star_of_square_neg_three hh,star_eq_inverse_of_norm_one hy]
  field_simp
  ring

theorem no_circle_root0 {h y : ℂ} (hh : h^2+3=0) (hy : ‖y‖=1) (hp : P0 h y=0) : False := by
  have hc : Pc0 h y=0 := by rw [reciprocal0 hh hy,hp,star_zero,mul_zero]
  have hb := bezout0 h y hh
  rw [hp,hc,mul_zero,mul_zero,zero_add] at hb
  exact zero_ne_one hb

theorem no_circle_root1 {h y : ℂ} (hh : h^2+3=0) (hy : ‖y‖=1) (hp : P1 h y=0) : False := by
  have hc : Pc1 h y=0 := by rw [reciprocal1 hh hy,hp,star_zero,mul_zero]
  have hb := bezout1 h y hh
  rw [hp,hc,mul_zero,mul_zero,zero_add] at hb
  exact zero_ne_one hb

theorem circle_root2 {h y : ℂ} (hh : h^2+3=0) (hy : ‖y‖=1) (hp : P2 h y=0) :
    y=-(h+1)/2 := by
  have hc : Pc2 h y=0 := by rw [reciprocal2 hh hy,hp,star_zero,mul_zero]
  have hb := bezout2 h y hh
  rw [hp,hc,mul_zero,mul_zero,zero_add] at hb
  linear_combination -hb

theorem no_circle_root3 {h y : ℂ} (hh : h^2+3=0) (hy : ‖y‖=1) (hp : P3 h y=0) : False := by
  have hc : Pc3 h y=0 := by rw [reciprocal3 hh hy,hp,star_zero,mul_zero]
  have hb := bezout3 h y hh
  rw [hp,hc,mul_zero,mul_zero,zero_add] at hb
  exact zero_ne_one hb

end CentralConfigurations.FiveBody.D2.Exceptional
