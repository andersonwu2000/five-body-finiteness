import CentralConfigurations.FiveBody.D2Regular.TorqueResponse

namespace CentralConfigurations.FiveBody.D2.Regular

theorem false_of_response_and_torque {k ell N T v y : ℂ}
    (hk : k≠0) (hell : ell≠0) (hN : N≠0) (hT : T≠0)
    (hz : N*((1+ell/2)*v+(3*k*ell/2)*y)=T)
    (hw : N*((3*ell/(2*k))*v+(1+ell/2)*y)=0)
    (ht : (-T/2)*y=0) : False := by
  have hy : y=0 := (mul_eq_zero.mp ht).resolve_left
    (div_ne_zero (neg_ne_zero.mpr hT) (by norm_num))
  have hw' := (mul_eq_zero.mp hw).resolve_left hN
  rw [hy,mul_zero,add_zero] at hw'
  have hv : v=0 := (mul_eq_zero.mp hw').resolve_left
    (div_ne_zero (mul_ne_zero (by norm_num) hell) (mul_ne_zero (by norm_num) hk))
  rw [hv,hy,mul_zero,mul_zero,add_zero,mul_zero] at hz
  exact hT hz.symm

end CentralConfigurations.FiveBody.D2.Regular
