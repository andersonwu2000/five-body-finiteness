import CentralConfigurations.FiveBody.D2Exceptional.EllZeroCertificate

namespace CentralConfigurations.FiveBody.D2.Exceptional
set_option maxHeartbeats 1000000

theorem real_affine_coefficients {x : ℂ} {A B : ℝ} (hx : x.im ≠ 0)
    (h : (A : ℂ)+(B : ℂ)*x=0) : A=0 ∧ B=0 := by
  have him := congrArg Complex.im h
  simp [Complex.mul_im] at him
  have hb : B=0 := him.resolve_right hx
  have hre := congrArg Complex.re h
  simp [hb] at hre
  exact ⟨hre,hb⟩

theorem rank0 {a b c x : ℂ} (hM : a+b+c ≠ 0) (hx : x ≠ 0) (hx1 : x ≠ 1)
    (hP : GapP0 a b c x=0) (hQ : GapQ0 a b c x=0) : RankK0 x=0 := by
  have h := rank_identity0 a b c x
  rw [hP,hQ,mul_zero,mul_zero,zero_add] at h
  have he : 2*x^5-6*x^4+6*x^3-2*x^2 = 2*x^2*(x-1)^3 := by ring
  rw [he] at h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hM)).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 3 (sub_ne_zero.mpr hx1)))

theorem rank1 {a b c x : ℂ} (hM : a+b+c ≠ 0) (hx : x ≠ 0) (hx1 : x ≠ 1)
    (hP : GapP1 a b c x=0) (hQ : GapQ1 a b c x=0) : RankK1 x=0 := by
  have h := rank_identity1 a b c x
  rw [hP,hQ,mul_zero,mul_zero,zero_add] at h
  have he : 2*x^6-6*x^5+6*x^4-2*x^3 = 2*x^3*(x-1)^3 := by ring
  rw [he] at h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hM)).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hx)) (pow_ne_zero 3 (sub_ne_zero.mpr hx1)))

theorem rank2 {a b c x : ℂ} (hM : a+b+c ≠ 0) (hx : x ≠ 0) (hx1 : x ≠ 1)
    (hP : GapP2 a b c x=0) (hQ : GapQ2 a b c x=0) : RankK2 x=0 := by
  have h := rank_identity2 a b c x
  rw [hP,hQ,mul_zero,mul_zero,zero_add] at h
  have he : 2*x^4-4*x^3+2*x^2 = 2*x^2*(x-1)^2 := by ring
  rw [he] at h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hM)).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hx)) (pow_ne_zero 2 (sub_ne_zero.mpr hx1)))

theorem rank3 {a b c x : ℂ} (hM : a+b+c ≠ 0) (hx : x ≠ 0) (hx1 : x ≠ 1)
    (hP : GapP3 a b c x=0) (hQ : GapQ3 a b c x=0) : RankK3 x=0 := by
  have h := rank_identity3 a b c x
  rw [hP,hQ,mul_zero,mul_zero,zero_add] at h
  have he : 2*x^5-4*x^4+2*x^3 = 2*x^3*(x-1)^2 := by ring
  rw [he] at h
  exact (mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hM)).resolve_left
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 3 hx)) (pow_ne_zero 2 (sub_ne_zero.mpr hx1)))

theorem rank0_nonreal {x : ℂ} (hk : RankK0 x=0) : x.im ≠ 0 := by
  intro hx
  have h := congrArg Complex.re hk
  simp [RankK0,pow_two,Complex.mul_re,hx] at h
  nlinarith [sq_nonneg (4*x.re-1)]

theorem rank1_nonreal {x : ℂ} (hk : RankK1 x=0) : x.im ≠ 0 := by
  intro hx
  have h := congrArg Complex.re hk
  simp [RankK1,pow_two,Complex.mul_re,hx] at h
  nlinarith [sq_nonneg (2*x.re-1)]

theorem rank3_nonreal {x : ℂ} (hk : RankK3 x=0) : x.im ≠ 0 := by
  intro hx
  have h := congrArg Complex.re hk
  simp [RankK3,pow_two,Complex.mul_re,hx] at h
  nlinarith [sq_nonneg (4*x.re-3)]

theorem mass_kernel0 {a b c : ℝ} {x : ℂ} (hM : a+b+c ≠ 0) (hx : x ≠ 0) (hx1 : x ≠ 1)
    (hP : GapP0 a b c x=0) (hQ : GapQ0 a b c x=0) : RankK0 x=0 ∧ a=c ∧ b=5*a := by
  have hMC : (a : ℂ)+b+c ≠ 0 := by exact_mod_cast hM
  have hk := rank0 hMC hx hx1 hP hQ
  have hred := Q_reduction0 (a : ℂ) b c x hk
  have haff : (((a-b)/4+c : ℝ) : ℂ)+(((5*a-b)/4 : ℝ) : ℂ)*x=0 := by
    rw [hQ] at hred
    push_cast
    linear_combination -hred
  obtain ⟨h0,h1⟩ := real_affine_coefficients (rank0_nonreal hk) haff
  exact ⟨hk,by linarith,by linarith⟩

theorem mass_kernel1 {a b c : ℝ} {x : ℂ} (hM : a+b+c ≠ 0) (hx : x ≠ 0) (hx1 : x ≠ 1)
    (hP : GapP1 a b c x=0) (hQ : GapQ1 a b c x=0) : RankK1 x=0 ∧ a=b ∧ c=5*a := by
  have hMC : (a : ℂ)+b+c ≠ 0 := by exact_mod_cast hM
  have hk := rank1 hMC hx hx1 hP hQ
  have hred := Q_reduction1 (a : ℂ) b c x hk
  have haff : ((3*a+2*b-c : ℝ) : ℂ)+((-a+b : ℝ) : ℂ)*x=0 := by
    rw [hQ] at hred
    push_cast
    linear_combination -hred
  obtain ⟨h0,h1⟩ := real_affine_coefficients (rank1_nonreal hk) haff
  exact ⟨hk,by linarith,by linarith⟩

theorem no_nonzero_mass_kernel2 {a b c x : ℂ} (hM : a+b+c ≠ 0) (hx : x ≠ 0) (hx1 : x ≠ 1)
    (hP : GapP2 a b c x=0) (hQ : GapQ2 a b c x=0) : False := by
  have hk := rank2 hM hx hx1 hP hQ
  have hred := Q_reduction2 a b c x hk
  rw [hQ] at hred
  apply hM
  linear_combination hred

theorem mass_kernel3 {a b c : ℝ} {x : ℂ} (hM : a+b+c ≠ 0) (hx : x ≠ 0) (hx1 : x ≠ 1)
    (hP : GapP3 a b c x=0) (hQ : GapQ3 a b c x=0) : RankK3 x=0 ∧ a=5*b ∧ b=c := by
  have hMC : (a : ℂ)+b+c ≠ 0 := by exact_mod_cast hM
  have hk := rank3 hMC hx hx1 hP hQ
  have hred := Q_reduction3 (a : ℂ) b c x hk
  have haff : ((-a/2+3*b/2+c : ℝ) : ℂ)+(((a-5*b)/4 : ℝ) : ℂ)*x=0 := by
    rw [hQ] at hred
    push_cast
    linear_combination -hred
  obtain ⟨h0,h1⟩ := real_affine_coefficients (rank3_nonreal hk) haff
  exact ⟨hk,by linarith,by linarith⟩

end CentralConfigurations.FiveBody.D2.Exceptional
