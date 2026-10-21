import CentralConfigurations.FiveBody.D6Butterfly.LeadingTorque

namespace CentralConfigurations.FiveBody.D6

theorem first_coefficient_algebra {a b d x y H K : ℂ} {c : Fin 8 → ℂ}
    (hq : a*(c 6+c 7)= -d*x*c 5) (hp : b*(c 2+c 3)= -d*y*c 4)
    (hz : b*c 2+b*c 3+d*c 4+2*a*c 0=0)
    (hw : 2*b*c 1+d*c 5+a*c 6+a*c 7=0) :
    firstTorqueCoefficient a b d c x y H K=
      -(3*d/2)*(c 5*(H^3+K^3)*(a-(a+b)*x)+c 4*(H^3-K^3)*(b-(a+b)*y)) := by
  dsimp [firstTorqueCoefficient,driftD,driftE,torqueCoefficient]
  linear_combination (a*(H^3+K^3)/2)*hw+(b*(H^3-K^3)/2)*hz-
    ((a+3*b)*(H^3+K^3)/2)*hq-((3*a+b)*(H^3-K^3)/2)*hp

theorem zero_center_limits {a b d : ℝ} (ha : 0<a) (hb : 0<b) (hd : 0<d)
    {c : Fin 8 → ℂ} {u : Fin 6 → ℂ} {H K : ℂ}
    (hs : WingStatic a b d c u) (hun : ∀ e, u e≠0)
    (hH : H^2= -1) (hK : K^2=1)
    (h0 : (d:ℂ)*c 4*c 5*(1-reciprocalZ u-reciprocalW u)=0)
    (h1 : firstTorqueCoefficient a b d c (reciprocalZ u) (reciprocalW u) H K=0) :
    c 4=0 ∧ c 5=0 := by
  obtain ⟨hx,hy,hq,hp,-,-⟩ := hs.reciprocal_data hun
  have hn : (d:ℂ)≠0 := by exact_mod_cast ne_of_gt hd
  have hxy : 1-reciprocalZ u-reciprocalW u≠0 := by
    intro h
    apply catalogue_sum_ne_one hx hy
    linear_combination -h
  have hprod : c 4*c 5=0 := by
    have hmul := (mul_eq_zero.mp h0).resolve_right hxy
    exact (mul_eq_zero.mp (by simpa only [mul_assoc] using hmul : (d:ℂ)*(c 4*c 5)=0)).resolve_left hn
  have hcubes := cross_cube_sums_ne hH hK
  have hax := catalogue_positive_linear_ne ha hb hx
  have hby := catalogue_positive_linear_ne hb ha hy
  have hfactor : (3*(d:ℂ)/2)≠0 := by exact div_ne_zero (mul_ne_zero (by norm_num) hn) (by norm_num)
  rw [first_coefficient_algebra hq hp hs.center_z hs.center_w] at h1
  rcases mul_eq_zero.mp hprod with hp0|hq0
  · refine ⟨hp0,?_⟩
    rw [hp0,zero_mul,zero_mul,add_zero] at h1
    have hh := (mul_eq_zero.mp h1).resolve_left (neg_ne_zero.mpr hfactor)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hax)).resolve_right hcubes.1
  · refine ⟨?_,hq0⟩
    rw [hq0,zero_mul,zero_mul,zero_add] at h1
    have hh := (mul_eq_zero.mp h1).resolve_left (neg_ne_zero.mpr hfactor)
    have hby' : (b:ℂ)-((a:ℂ)+b)*reciprocalW u≠0 := by simpa only [add_comm] using hby
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hh).resolve_right hby')).resolve_right hcubes.2

end CentralConfigurations.FiveBody.D6
