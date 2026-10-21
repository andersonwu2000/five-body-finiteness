import CentralConfigurations.FiveBody.D2Exceptional.GapRows

namespace CentralConfigurations.FiveBody.D2.Exceptional
set_option maxHeartbeats 2000000

theorem gap_sign_swap12 (a b c x : ℂ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    gapEuler a c b (1/x) 1 (-1) = -x*gapEuler a b c x 1 1 ∧
    gapTrace a c b (1/x) 1 (-1) = x^3*gapTrace a b c x 1 1 ∧
    gapLambda a c b (1/x) 1 (-1) = x^3*gapLambda a b c x 1 1+
      x^2*gapEuler a b c x 1 1 := by
  have hfrac : 1/x-1 = -(x-1)/x := by field_simp [hx]; ring
  have hinv : 1/x-1 ≠ 0 := by
    intro h
    have hh := congrArg (fun z => x*z) h
    field_simp [hx] at hh
    exact hx1 (by linear_combination -hh)
  constructor
  · dsimp [gapEuler,gapLambda]
    rw [hfrac]
    field_simp [hx,sub_ne_zero.mpr hx1,hinv]
    ring
  constructor
  · dsimp [gapTrace]
    rw [hfrac]
    field_simp [hx,sub_ne_zero.mpr hx1,hinv]
    ring
  · dsimp [gapEuler,gapLambda]
    rw [hfrac]
    field_simp [hx,sub_ne_zero.mpr hx1,hinv]
    ring

theorem gap_sign_swap01 (a b c x : ℂ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    gapEuler b a c (1-x) (-1) (-1) = -gapEuler a b c x 1 1 ∧
    gapTrace b a c (1-x) (-1) (-1) = gapTrace a b c x 1 1 ∧
    gapLambda b a c (1-x) (-1) (-1) = gapLambda a b c x 1 1 := by
  have hshift : 1-x ≠ 0 := by simpa [sub_eq_zero] using Ne.symm hx1
  have hshift1 : 1-x-1 ≠ 0 := by simpa using neg_ne_zero.mpr hx
  constructor
  · dsimp [gapEuler,gapLambda]
    field_simp [hx,sub_ne_zero.mpr hx1,hshift,hshift1]
    ring
  constructor
  · dsimp [gapTrace]
    field_simp [hx,sub_ne_zero.mpr hx1,hshift,hshift1]
    ring
  · dsimp [gapLambda]
    field_simp [hx,sub_ne_zero.mpr hx1,hshift,hshift1]
    ring

end CentralConfigurations.FiveBody.D2.Exceptional
