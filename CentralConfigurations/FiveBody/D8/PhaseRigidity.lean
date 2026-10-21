import CentralConfigurations.FiveBody.D8.UpperChart

namespace CentralConfigurations.FiveBody.D8

/-- Positivity of the masses eliminates the two primitive cubic phases.
No sign is assigned to an inverse distance. -/
theorem positive_cubic_phase (p q c : ℝ) (hp : 0<p) (hq : 0<q) (hc : 0<c)
    (k : ℂ) (hk : k^3=1)
    (he : (c:ℂ)^2*((p:ℂ)+q)*((p:ℂ)+q*k)^3=(p:ℂ)^3*(q:ℂ)^3) : k=1 := by
  by_contra hn
  have hk2 : k^2+k+1=0 := by
    have h : (k-1)*(k^2+k+1)=0 := by linear_combination hk
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hn)
  have him : k.im≠0 := by
    intro hi
    have h := congrArg Complex.re hk2
    simp [Complex.add_re,Complex.mul_re,pow_two,hi] at h
    nlinarith [sq_nonneg (k.re+1/2)]
  have hexpand : ((p:ℂ)+q*k)^3=(p:ℂ)^3+q^3-3*p*q^2+3*p*q*(p-q)*k := by
    linear_combination (q:ℂ)^3*hk+3*(p:ℂ)*q^2*hk2
  rw [hexpand] at he
  have hei := congrArg Complex.im he
  simp [← Complex.ofReal_pow,Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im] at hei
  have heq : p=q := by
    simpa [ne_of_gt hc,ne_of_gt hp,ne_of_gt hq,ne_of_gt (add_pos hp hq),him,sub_eq_zero] using hei
  subst q
  have her := congrArg Complex.re he
  simp [← Complex.ofReal_pow,Complex.add_re,Complex.sub_re,Complex.mul_re] at her
  nlinarith [mul_pos (pow_pos hc 2) (pow_pos hp 4),pow_pos hp 6]

/-- A signed upper triangle on the positive-mass phase has one common root ratio. -/
theorem upper_phase_rigidity (p q c : ℝ) (hp : 0<p) (hq : 0<q) (hc : 0<c)
    (U V : ℂ) (hU : U≠0) (hV : V≠0)
    (hUc : U^3= -((p:ℂ)+q)/c) (hVc : V^3= -((p:ℂ)+q)/c)
    (hmetric : (p:ℂ)*q*U^2*V^2=((p:ℂ)+q)*(p*V^2+q*U^2)) :
    U=V ∧ U^2*(p:ℂ)*q=((p:ℂ)+q)^2 ∧ (c:ℂ)*U^3= -((p:ℂ)+q) := by
  have hpn : (p:ℂ)≠0 := by exact_mod_cast ne_of_gt hp
  have hqn : (q:ℂ)≠0 := by exact_mod_cast ne_of_gt hq
  have hcn : (c:ℂ)≠0 := by exact_mod_cast ne_of_gt hc
  have hhn : (p:ℂ)+q≠0 := by exact_mod_cast ne_of_gt (add_pos hp hq)
  let k := V/U
  have hk : k^3=1 := by dsimp [k]; rw [div_pow,hVc,← hUc]; exact div_self (pow_ne_zero 3 hU)
  have hVeq : V=k*U := by dsimp [k]; field_simp
  have hshape : U^2*(p:ℂ)*q=((p:ℂ)+q)*((p:ℂ)+q*k) := by
    have he := hmetric
    rw [hVeq] at he
    have hh : U^2*(U^2*(p:ℂ)*q-((p:ℂ)+q)*((p:ℂ)+q*k))=0 := by
      linear_combination k*he-(p:ℂ)*q*U^4*hk+((p:ℂ)+q)*p*U^2*hk
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (pow_ne_zero 2 hU))
  have hcu : (c:ℂ)*U^3= -((p:ℂ)+q) := by rw [hUc]; field_simp
  have hpol : (c:ℂ)^2*((p:ℂ)+q)*((p:ℂ)+q*k)^3=(p:ℂ)^3*q^3 := by
    apply (mul_left_cancel₀ (pow_ne_zero 2 hhn))
    calc
      _ = (c:ℂ)^2*(U^2*p*q)^3 := by rw [hshape]; ring
      _ = ((c:ℂ)*U^3)^2*(p:ℂ)^3*q^3 := by ring
      _ = _ := by rw [hcu]; ring
  have hk1 := positive_cubic_phase p q c hp hq hc k hk hpol
  refine ⟨?_,?_,hcu⟩
  · simpa only [hk1,one_mul] using hVeq.symm
  · simpa only [hk1,mul_one,pow_two] using hshape

end CentralConfigurations.FiveBody.D8
