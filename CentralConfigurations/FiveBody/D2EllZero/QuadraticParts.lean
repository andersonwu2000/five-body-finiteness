import CentralConfigurations.FiveBody.D2Exceptional.EllZeroMass

namespace CentralConfigurations.FiveBody.D2.EllZero
open Exceptional

theorem rank0_parts {x : ℂ} (hk : RankK0 x=0) : x.re=1/4 ∧ x.im^2=7/16 := by
  have hi := congrArg Complex.im hk
  have hr := congrArg Complex.re hk
  simp [RankK0,pow_two,Complex.mul_im,Complex.mul_re] at hi hr
  have hp : x.im*(4*x.re-1)=0 := by linear_combination hi
  have hreal : x.re=1/4 := by
    have h := (mul_eq_zero.mp hp).resolve_left (rank0_nonreal hk)
    linarith
  exact ⟨hreal,by rw [hreal] at hr; nlinarith⟩

theorem rank1_parts {x : ℂ} (hk : RankK1 x=0) : x.re=1/2 ∧ x.im^2=7/4 := by
  have hi := congrArg Complex.im hk
  have hr := congrArg Complex.re hk
  simp [RankK1,pow_two,Complex.mul_im,Complex.mul_re] at hi hr
  have hp : x.im*(2*x.re-1)=0 := by linear_combination hi
  have hreal : x.re=1/2 := by
    have h := (mul_eq_zero.mp hp).resolve_left (rank1_nonreal hk)
    linarith
  exact ⟨hreal,by rw [hreal] at hr; nlinarith⟩

theorem rank3_parts {x : ℂ} (hk : RankK3 x=0) : x.re=3/4 ∧ x.im^2=7/16 := by
  have hi := congrArg Complex.im hk
  have hr := congrArg Complex.re hk
  simp [RankK3,pow_two,Complex.mul_im,Complex.mul_re] at hi hr
  have hp : x.im*(4*x.re-3)=0 := by linear_combination hi
  have hreal : x.re=3/4 := by
    have h := (mul_eq_zero.mp hp).resolve_left (rank3_nonreal hk)
    linarith
  exact ⟨hreal,by rw [hreal] at hr; nlinarith⟩

end CentralConfigurations.FiveBody.D2.EllZero
