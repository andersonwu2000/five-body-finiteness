import CentralConfigurations.FiveBody.D2Exceptional.HZeroCircle

namespace CentralConfigurations.FiveBody.D2.Exceptional

def eulerQuintic (ω y s13 s23 : ℂ) : ℂ :=
  y*(y-ω)^2*(y-1)^2+(ω-1)^2*(s23*(y-1)^2-ω*s13*(y-ω)^2)

theorem quintic_of_original_rows {a b c lam ω y s13 s23 : ℂ}
    (hc : c ≠ 0) (hω : ω ≠ 1) (hy : y ≠ 1) (hyω : y ≠ ω)
    (hcenter : a+b*ω+c*y=0)
    (h0 : lam = -b/(ω-1)^2-c*s13/(y-1)^2)
    (h1 : lam*ω = a/(ω-1)^2-c*s23/(y-ω)^2) : eulerQuintic ω y s13 s23 = 0 := by
  have hP : c*eulerQuintic ω y s13 s23 = 0 := by
    dsimp [eulerQuintic]
    field_simp [sub_ne_zero.mpr hω,sub_ne_zero.mpr hy,sub_ne_zero.mpr hyω] at h0 h1
    linear_combination -ω*(y-ω)^2*h0+(y-1)^2*h1+(y-1)^2*(y-ω)^2*hcenter
  exact (mul_eq_zero.mp hP).resolve_left hc

end CentralConfigurations.FiveBody.D2.Exceptional
