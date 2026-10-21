import CentralConfigurations.FiveBody.D6Butterfly.WingRigidity

namespace CentralConfigurations.FiveBody.D6

/-- Both primitive cube roots and all overall inverse-distance signs remain
in this compressed catalogue. Its variable is the reciprocal wing ratio. -/
theorem wing_reciprocal_catalogue {R F G : ℂ}
    (hR : R≠0) (hF : F≠0) (hG : G≠0) (hFG : F^3=G^3)
    (hL : R⁻¹^2-2*F⁻¹^2-2*G⁻¹^2=0) :
    (F^3/R^3)^2=64 ∨ (F^3/R^3)^2= -8 := by
  let ξ := F^2/G^2
  have hξ : ξ^3=1 := by
    dsimp [ξ]
    rw [div_pow]
    have hpow (z : ℂ) : (z^2)^3=(z^3)^2 := by ring
    rw [hpow F,hpow G,hFG]
    exact div_self (pow_ne_zero _ (pow_ne_zero _ hG))
  have hc : F^2=2*R^2*(1+ξ) := by
    dsimp [ξ]
    field_simp [hR,hF,hG] at hL ⊢
    linear_combination hL
  have hx : (F^3/R^3)^2=8*(1+ξ)^3 := by
    have h := congrArg (fun z : ℂ => z^3) hc
    field_simp [hR]
    linear_combination h
  have hfac : (ξ-1)*(ξ^2+ξ+1)=0 := by linear_combination hξ
  rcases mul_eq_zero.mp hfac with h|h
  · left
    have he : ξ=1 := sub_eq_zero.mp h
    norm_num [hx,he]
  · right
    rw [hx]
    linear_combination 8*hξ+24*h

theorem catalogue_sum_ne_one {x y : ℂ}
    (hx : x^2=64 ∨ x^2= -8) (hy : y^2=64 ∨ y^2= -8) : x+y≠1 := by
  intro hsum
  have h64 (z : ℂ) (hz : z^2=64) : z=8 ∨ z= -8 :=
    eq_or_eq_neg_of_sq_eq_sq z 8 (by norm_num; exact hz)
  rcases hx with hx|hx <;> rcases hy with hy|hy
  · rcases h64 x hx with rfl|rfl <;> rcases h64 y hy with rfl|rfl <;> norm_num at hsum
  · rcases h64 x hx with rfl|rfl
    · have he : y= -7 := by linear_combination hsum
      norm_num [he] at hy
    · have he : y=9 := by linear_combination hsum
      norm_num [he] at hy
  · rcases h64 y hy with rfl|rfl
    · have he : x= -7 := by linear_combination hsum
      norm_num [he] at hx
    · have he : x=9 := by linear_combination hsum
      norm_num [he] at hx
  · have he : x=(1/2:ℂ) := by
      linear_combination (hx-hy+(y-x+1)*hsum)/2
    norm_num [he] at hx

theorem catalogue_positive_linear_ne {x : ℂ} {a b : ℝ} (ha : 0<a) (hb : 0<b)
    (hx : x^2=64 ∨ x^2= -8) : (a:ℂ)-(a+b)*x≠0 := by
  intro h
  have hab : a+b≠0 := ne_of_gt (add_pos ha hb)
  have habC : (a:ℂ)+b≠0 := by exact_mod_cast hab
  have he : x=((a/(a+b):ℝ):ℂ) := by
    push_cast
    field_simp [habC]
    linear_combination -h
  have hc0 : 0<a/(a+b) := div_pos ha (add_pos ha hb)
  have hc1 : a/(a+b)<1 := (div_lt_one (add_pos ha hb)).mpr (by linarith)
  rw [he] at hx
  rcases hx with hx|hx
  · have hsq : (a/(a+b))^2=64 := by exact_mod_cast hx
    nlinarith
  · have hsq : (a/(a+b))^2= -8 := by exact_mod_cast hx
    nlinarith [sq_nonneg (a/(a+b))]

end CentralConfigurations.FiveBody.D6
