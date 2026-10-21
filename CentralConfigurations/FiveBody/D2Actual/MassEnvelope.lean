import CentralConfigurations.FiveBody.D9Mass

/-! The complete disconnected pair/triangle envelope, for every positive mass. -/
namespace CentralConfigurations.FiveBody.D2
open D9
set_option maxHeartbeats 1000000

theorem disconnected_envelope_gap {A B X Y : ℝ}
    (hA : 0 < A) (hB : 0 < B) (_hX : 0 ≤ X) (_hY : 0 ≤ Y)
    (hXA : X ≤ A ^ 2 / 4) (hYB : Y ≤ B ^ 2 / 3) :
    cubeRoot (A + B) * (X / cubeRoot A + Y / cubeRoot B) < X + Y + A * B := by
  let a := cubeRoot A
  let b := cubeRoot B
  let u := cubeRoot (A+B)
  have ha : 0 < a := cubeRoot_pos hA
  have hb : 0 < b := cubeRoot_pos hB
  have hu : 0 < u := cubeRoot_pos (add_pos hA hB)
  have ha3 : a^3 = A := cubeRoot_cube hA.le
  have hb3 : b^3 = B := cubeRoot_cube hB.le
  have hu3 : u^3 = A+B := cubeRoot_cube (add_pos hA hB).le
  have hau : a < u := cube_strict (by rw [ha3,hu3]; linarith)
  have hbu : b < u := cube_strict (by rw [hb3,hu3]; linarith)
  have hgapA : a^5*(u-a) ≤ A*B := by
    have hid : A*B-a^5*(u-a) = a^3*(u-a)*(u^2+u*a) := by
      linear_combination -a^3*hu3 + (a^3-B)*ha3
    have hn : 0 ≤ a^3*(u-a)*(u^2+u*a) :=
      mul_nonneg (mul_nonneg (pow_pos ha 3).le (sub_pos.mpr hau).le)
        (add_nonneg (sq_nonneg _) (mul_pos hu ha).le)
    linarith
  have hgapB : b^5*(u-b) ≤ A*B := by
    have hid : A*B-b^5*(u-b) = b^3*(u-b)*(u^2+u*b) := by
      linear_combination -b^3*hu3 + (b^3-A)*hb3
    have hn : 0 ≤ b^3*(u-b)*(u^2+u*b) :=
      mul_nonneg (mul_nonneg (pow_pos hb 3).le (sub_pos.mpr hbu).le)
        (add_nonneg (sq_nonneg _) (mul_pos hu hb).le)
    linarith
  have hboundA : X*u/a ≤ X+A*B/4 := by
    have hc := mul_le_mul_of_nonneg_right hXA (div_nonneg (sub_nonneg.mpr hau.le) ha.le)
    have hid : (A^2/4)*((u-a)/a) = a^5*(u-a)/4 := by
      rw [← ha3]
      field_simp
    rw [hid] at hc
    have he : X*u/a = X+X*((u-a)/a) := by field_simp; ring
    rw [he]
    linarith
  have hboundB : Y*u/b ≤ Y+A*B/3 := by
    have hc := mul_le_mul_of_nonneg_right hYB (div_nonneg (sub_nonneg.mpr hbu.le) hb.le)
    have hid : (B^2/3)*((u-b)/b) = b^5*(u-b)/3 := by
      rw [← hb3]
      field_simp
    rw [hid] at hc
    have he : Y*u/b = Y+Y*((u-b)/b) := by field_simp; ring
    rw [he]
    linarith
  change u*(X/a+Y/b) < X+Y+A*B
  have he : u*(X/a+Y/b) = X*u/a+Y*u/b := by ring
  rw [he]
  have hAB : 0 < A*B := mul_pos hA hB
  linarith

theorem five_mass_envelope_gap {m : Fin 5 → ℝ} (hm : ∀ i, 0 < m i) :
    cubeRoot (m 0+m 1+m 2+m 3+m 4) *
      (m 3*m 4/cubeRoot (m 3+m 4) +
        (m 0*m 1+m 0*m 2+m 1*m 2)/cubeRoot (m 0+m 1+m 2)) <
      m 3*m 4+(m 0*m 1+m 0*m 2+m 1*m 2)+(m 3+m 4)*(m 0+m 1+m 2) := by
  have hA : 0 < m 3+m 4 := add_pos (hm 3) (hm 4)
  have hB : 0 < m 0+m 1+m 2 := add_pos (add_pos (hm 0) (hm 1)) (hm 2)
  have hX : 0 ≤ m 3*m 4 := (mul_pos (hm 3) (hm 4)).le
  have hY : 0 ≤ m 0*m 1+m 0*m 2+m 1*m 2 :=
    add_nonneg (add_nonneg (mul_pos (hm 0) (hm 1)).le (mul_pos (hm 0) (hm 2)).le)
      (mul_pos (hm 1) (hm 2)).le
  have hXA : m 3*m 4 ≤ (m 3+m 4)^2/4 := by nlinarith [sq_nonneg (m 3-m 4)]
  have hYB : m 0*m 1+m 0*m 2+m 1*m 2 ≤ (m 0+m 1+m 2)^2/3 := by
    nlinarith [sq_nonneg (m 0-m 1), sq_nonneg (m 0-m 2), sq_nonneg (m 1-m 2)]
  convert disconnected_envelope_gap hA hB hX hY hXA hYB using 1
  congr 2
  ring

end CentralConfigurations.FiveBody.D2
