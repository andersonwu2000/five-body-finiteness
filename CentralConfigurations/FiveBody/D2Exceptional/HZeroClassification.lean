import CentralConfigurations.FiveBody.D2Exceptional.HZeroQuinticIdentity

namespace CentralConfigurations.FiveBody.D2.Exceptional

theorem normalized_circle_classification {h y s13 s23 : ℂ}
    (hh : h^2+3=0) (hy : ‖y‖=1)
    (hs13 : s13=1 ∨ s13=-1) (hs23 : s23=1 ∨ s23=-1)
    (hP : eulerQuintic ((h-1)/2) y s13 s23=0) :
    s13=-1 ∧ s23=1 ∧ y=-(h+1)/2 := by
  rcases hs13 with rfl | rfl <;> rcases hs23 with rfl | rfl
  · have hp : P0 h y=0 := by rw [normalized_quintic0 h y hh]; exact hP
    exact False.elim (no_circle_root0 hh hy hp)
  · have hp : P1 h y=0 := by rw [normalized_quintic1 h y hh]; exact hP
    exact False.elim (no_circle_root1 hh hy hp)
  · have hp : P2 h y=0 := by rw [normalized_quintic2 h y hh]; exact hP
    exact ⟨rfl,rfl,circle_root2 hh hy hp⟩
  · have hp : P3 h y=0 := by rw [normalized_quintic3 h y hh]; exact hP
    exact False.elim (no_circle_root3 hh hy hp)

theorem surviving_center_equal_masses {h : ℂ} {a b c : ℝ}
    (hh : h^2+3=0)
    (hcenter : (a : ℂ)+(b : ℂ)*((h-1)/2)+(c : ℂ)*(-(h+1)/2)=0) :
    a=c ∧ b=c := by
  have hstar := congrArg Complex.re (star_of_square_neg_three hh)
  simp at hstar
  have hre0 : h.re=0 := by linarith
  have hsquare := congrArg Complex.re hh
  simp [pow_two,Complex.mul_re,hre0] at hsquare
  have him0 : h.im ≠ 0 := by intro he; simp [he] at hsquare
  have hlin : (2*(a : ℂ)-(b : ℂ)-c)+((b : ℂ)-c)*h=0 := by
    linear_combination 2*hcenter
  have him := congrArg Complex.im hlin
  simp [Complex.mul_im] at him
  have hbc := sub_eq_zero.mp (him.resolve_right him0)
  have hre := congrArg Complex.re hlin
  simp [Complex.mul_re,hre0] at hre
  exact ⟨by linarith, hbc⟩

theorem surviving_inertia_zero {h : ℂ} (a : ℂ) (hh : h^2+3=0) :
    a*(1^2+((h-1)/2)^2+(-(h+1)/2)^2)=0 := by
  linear_combination (a/2)*hh

end CentralConfigurations.FiveBody.D2.Exceptional
