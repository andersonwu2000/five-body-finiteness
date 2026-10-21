import CentralConfigurations.FiveBody.D2Exceptional.GapRows
import CentralConfigurations.FiveBody.D2Exceptional.EllZeroCertificate

namespace CentralConfigurations.FiveBody.D2.Exceptional
set_option maxHeartbeats 2000000

theorem clear_euler0 (a b c x : ℂ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    GapP0 a b c x = x^2*(x-1)^2*gapEuler a b c x 1 1 := by
  dsimp [GapP0,gapEuler,gapLambda]
  field_simp [hx,sub_ne_zero.mpr hx1]
  ring

theorem clear_trace0 (a b c x : ℂ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    GapQ0 a b c x = x^3*(x-1)^3*(gapTrace a b c x 1 1-
      gapLambda a b c x 1 1) := by
  dsimp [GapQ0,gapTrace,gapLambda]
  field_simp [hx,sub_ne_zero.mpr hx1]
  ring

theorem clear_euler1 (a b c x : ℂ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    GapP1 a b c x = x^2*(x-1)^2*gapEuler a b c x 1 (-1) := by
  dsimp [GapP1,gapEuler,gapLambda]
  field_simp [hx,sub_ne_zero.mpr hx1]
  ring

theorem clear_trace1 (a b c x : ℂ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    GapQ1 a b c x = x^3*(x-1)^3*(gapTrace a b c x 1 (-1)-
      gapLambda a b c x 1 (-1)) := by
  dsimp [GapQ1,gapTrace,gapLambda]
  field_simp [hx,sub_ne_zero.mpr hx1]
  ring

theorem clear_euler2 (a b c x : ℂ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    GapP2 a b c x = x^2*(x-1)^2*gapEuler a b c x (-1) 1 := by
  dsimp [GapP2,gapEuler,gapLambda]
  field_simp [hx,sub_ne_zero.mpr hx1]
  ring

theorem clear_trace2 (a b c x : ℂ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    GapQ2 a b c x = x^3*(x-1)^3*(gapTrace a b c x (-1) 1-
      gapLambda a b c x (-1) 1) := by
  dsimp [GapQ2,gapTrace,gapLambda]
  field_simp [hx,sub_ne_zero.mpr hx1]
  ring

theorem clear_euler3 (a b c x : ℂ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    GapP3 a b c x = x^2*(x-1)^2*gapEuler a b c x (-1) (-1) := by
  dsimp [GapP3,gapEuler,gapLambda]
  field_simp [hx,sub_ne_zero.mpr hx1]
  ring

theorem clear_trace3 (a b c x : ℂ) (hx : x ≠ 0) (hx1 : x ≠ 1) :
    GapQ3 a b c x = x^3*(x-1)^3*(gapTrace a b c x (-1) (-1)-
      gapLambda a b c x (-1) (-1)) := by
  dsimp [GapQ3,gapTrace,gapLambda]
  field_simp [hx,sub_ne_zero.mpr hx1]
  ring

end CentralConfigurations.FiveBody.D2.Exceptional
