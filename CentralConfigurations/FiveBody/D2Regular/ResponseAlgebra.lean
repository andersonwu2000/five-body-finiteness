import CentralConfigurations.FiveBody.D2Regular.WeightedPlane

namespace CentralConfigurations.FiveBody.D2.Regular

/-- Exact determinant of the transverse two by two block. -/
theorem transverse_determinant (k ell : ℂ) (hk : k≠0) :
    (1+ell/2)^2-(3*k*ell/2)*(3*ell/(2*k))=(1-ell)*(1+2*ell) := by
  field_simp [hk]
  ring

theorem regular_transverse_response {k ell v y h : ℂ}
    (hk : k≠0) (h1 : ell≠1) (h2 : ell≠ -(1/2:ℂ))
    (hz : (1+ell/2)*v+(3*k*ell/2)*y=h)
    (hw : (3*ell/(2*k))*v+(1+ell/2)*y=0) :
    y= -3*ell*h/(2*k*(1-ell)*(1+2*ell)) := by
  have he1 : 1-ell≠0 := sub_ne_zero.mpr h1.symm
  have he2 : 1+2*ell≠0 := by intro hh; apply h2; linear_combination hh/2
  field_simp [hk] at hw
  apply (eq_div_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hk) he1) he2)).2
  linear_combination (2+ell)/2*hw-3*ell*hz

/-- The source's selected three rows have zero kernel. S and N are the two
nonzero bilinear norms; e2/d2 is the exact coordinate gauge correction. -/
theorem selected_shape_rows_injective {k ell S N e2 d2 u v y : ℂ}
    (hk : k≠0) (h1 : ell≠1) (h2 : ell≠ -(1/2:ℂ))
    (hS : S≠0) (hN : N≠0)
    (hd : S*(3*u/(2*k)-3*e2*y/(2*d2))=0)
    (hz : N*((1+ell/2)*v+(3*k*ell/2)*y)=0)
    (hw : N*((3*ell/(2*k))*v+(1+ell/2)*y)=0) : u=0 ∧ v=0 ∧ y=0 := by
  have hz' := (mul_eq_zero.mp hz).resolve_left hN
  have hw' := (mul_eq_zero.mp hw).resolve_left hN
  have hy := regular_transverse_response hk h1 h2 hz' hw'
  simp only [mul_zero,zero_div] at hy
  have hv : v=0 := by
    rw [hy,mul_zero,add_zero] at hz' hw'
    have hh : v=0 := by
      field_simp [hk] at hw'
      linear_combination hz'-hw'/6
    exact hh
  have hu := (mul_eq_zero.mp hd).resolve_left hS
  rw [hy,mul_zero,zero_div,sub_zero] at hu
  have hu' : u=0 := by
    field_simp [hk] at hu
    linear_combination hu/3
  exact ⟨hu',hv,hy⟩

/-- Once full first response is obtained, this is the unused original torque
coefficient. The scalar is allowed to be complex and every phase remains. -/
theorem regular_torque_coefficient {k ell N h v y : ℂ}
    (hk : k≠0) (h1 : ell≠1) (h2 : ell≠ -(1/2:ℂ))
    (hz : (1+ell/2)*v+(3*k*ell/2)*y=h)
    (hw : (3*ell/(2*k))*v+(1+ell/2)*y=0) :
    -(h*y*N)/2=3*ell*(h^2*N)/(4*k*(1-ell)*(1+2*ell)) := by
  rw [regular_transverse_response hk h1 h2 hz hw]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

end CentralConfigurations.FiveBody.D2.Regular
