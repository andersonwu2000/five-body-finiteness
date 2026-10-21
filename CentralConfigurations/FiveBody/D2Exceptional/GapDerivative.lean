import CentralConfigurations.FiveBody.D2Exceptional.GapRows
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace CentralConfigurations.FiveBody.D2.Exceptional
set_option maxHeartbeats 2000000

theorem gapEuler_hasDerivAt (a b c s13 s23 x : ℂ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    HasDerivAt (fun y => gapEuler a b c y s13 s23)
      (gapLambda a b c x s13 s23-2*gapTrace a b c x s13 s23) x := by
  have hid := hasDerivAt_id x
  have hshift := hid.sub_const 1
  have hI : HasDerivAt (fun y : ℂ => 1/y^2) (-2/x^3) x := by
    convert (hid.pow 2).inv (pow_ne_zero 2 hx) using 1
    · funext y; simp
    · dsimp
      field_simp [hx]
  have hJ : HasDerivAt (fun y : ℂ => 1/(y-1)^2) (-2/(x-1)^3) x := by
    convert (hshift.pow 2).inv (pow_ne_zero 2 (sub_ne_zero.mpr hx1)) using 1
    · funext y; simp
    · dsimp
      field_simp [sub_ne_zero.mpr hx1]
  have hL : HasDerivAt (fun y => gapLambda a b c y s13 s23)
      (c*(s13*(-2/x^3)-s23*(-2/(x-1)^3))) x := by
    simpa [gapLambda,div_eq_mul_inv] using
      (((hI.const_mul s13).sub (hJ.const_mul s23)).const_mul c).const_add (a+b)
  have h := ((hI.const_mul ((a+c)*s13)).add
      ((hJ.const_mul s23).const_add 1 |>.const_mul b)).sub (hid.mul hL)
  convert h using 1
  · funext y
    simp [gapEuler,div_eq_mul_inv]
  · dsimp [gapLambda,gapTrace]
    field_simp [hx,sub_ne_zero.mpr hx1]
    ring

theorem GapData.resonant_derivative_zero {mass : Fin 3 → ℂ}
    {r : ZWSystem ℂ 3 mass} (d : GapData r)
    (hell : transverseEigenvalue r = -(1/2 : ℂ)) :
    HasDerivAt (fun y => gapEuler (mass 0) (mass 1) (mass 2) y d.sign13 d.sign23) 0 d.x := by
  have h := gapEuler_hasDerivAt (mass 0) (mass 1) (mass 2) d.sign13 d.sign23 d.x
    d.x_ne_zero d.x_ne_one
  have ht := d.trace
  change transverseEigenvalue r =
    gapTrace (mass 0) (mass 1) (mass 2) d.x d.sign13 d.sign23/d.lam-1 at ht
  rw [hell] at ht
  field_simp [d.lam_ne_zero] at ht
  have hz : gapLambda (mass 0) (mass 1) (mass 2) d.x d.sign13 d.sign23-
      2*gapTrace (mass 0) (mass 1) (mass 2) d.x d.sign13 d.sign23=0 := by
    rw [← d.original_rows.1]
    linear_combination ht
  rwa [hz] at h

end CentralConfigurations.FiveBody.D2.Exceptional
