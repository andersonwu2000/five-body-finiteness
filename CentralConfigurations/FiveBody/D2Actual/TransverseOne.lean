import CentralConfigurations.FiveBody.D2Actual.EulerResidual

/-! The ell=1 Euler overlap is the equal-cube sector, from exact three-body rows. -/
namespace CentralConfigurations.FiveBody.D2
open scoped BigOperators
set_option maxHeartbeats 2000000

def transverseEigenvalue {mass : Fin 3 → ℂ} (r : ZWSystem ℂ 3 mass) : ℂ :=
  (mass 0+mass 1)*r.delta 0 1^3+(mass 0+mass 2)*r.delta 0 2^3+
    (mass 1+mass 2)*r.delta 1 2^3-1

theorem equal_cube_of_transverse_one {mass : Fin 3 → ℂ}
    (r : ZWSystem ℂ 3 mass) (hm : ∀ i, mass i ≠ 0)
    (hM : mass 0+mass 1+mass 2 ≠ 0)
    (hS : (∑ i, mass i*r.w i^2) ≠ 0) (hell : transverseEigenvalue r = 1) :
    ∀ i j, i ≠ j → (mass 0+mass 1+mass 2)*r.delta i j^3 = 1 := by
  let B := mass 0+mass 1+mass 2
  let S := ∑ i, mass i*r.w i^2
  let a := r.w 0-r.w 1
  let b := r.w 0-r.w 2
  let c := r.w 1-r.w 2
  let x := B*r.delta 0 1^3-1
  let y := B*r.delta 0 2^3-1
  let z := B*r.delta 1 2^3-1
  have h0 : mass 1*x*a+mass 2*y*b = 0 := r.swap.three_body_reduced_z_row_zero
  have h1 : -mass 0*x*a+mass 2*z*c = 0 := by
    have h := r.swap.three_body_reduced_z_row_one
    change mass 0*x*(r.w 1-r.w 0)+mass 2*z*c = 0 at h
    linear_combination h
  have htrace : (mass 0+mass 1)*x+(mass 0+mass 2)*y+(mass 1+mass 2)*z = 0 := by
    dsimp [transverseEigenvalue] at hell
    dsimp [x,y,z,B]
    linear_combination (mass 0+mass 1+mass 2)*hell
  have hcenter := r.mass_center_w
  simp [Fin.sum_univ_succ] at hcenter
  have hdet :
      -mass 1*mass 2*a*c*(mass 0+mass 2)+mass 0*mass 2*a*b*(mass 1+mass 2)+
        mass 2^2*b*c*(mass 0+mass 1) = mass 2*B*S := by
    dsimp [a,b,c,B,S]
    simp [Fin.sum_univ_succ]
    linear_combination -mass 2*(mass 0*r.w 0+mass 1*r.w 1+mass 2*r.w 2)*hcenter
  have hx : mass 2*B*S*x = 0 := by
    rw [← hdet]
    linear_combination -mass 2*c*(mass 0+mass 2)*h0 -
      mass 2*b*(mass 1+mass 2)*h1 + mass 2^2*b*c*htrace
  have hx0 : x = 0 :=
    (mul_eq_zero.mp hx).resolve_left (mul_ne_zero (mul_ne_zero (hm 2) hM) hS)
  have hy0 : y = 0 := by
    rw [hx0, mul_zero, zero_mul, zero_add] at h0
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right
      (r.w_separation_ne_zero (by decide : (0 : Fin 3) ≠ 2)))).resolve_left (hm 2)
  have hz0 : z = 0 := by
    rw [hx0, mul_zero, zero_mul, zero_add] at h1
    exact (mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right
      (r.w_separation_ne_zero (by decide : (1 : Fin 3) ≠ 2)))).resolve_left (hm 2)
  have h01 : B*r.delta 0 1^3 = 1 := sub_eq_zero.mp hx0
  have h02 : B*r.delta 0 2^3 = 1 := sub_eq_zero.mp hy0
  have h12 : B*r.delta 1 2^3 = 1 := sub_eq_zero.mp hz0
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [r.delta_symm 1 0,r.delta_symm 2 0,r.delta_symm 2 1,B]

theorem ActualLimit.transverse_ne_one {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
    (s : ActualLimit m q l (I0 : ℂ)) (hm : ∀ i, 0 < m i)
    (hphysical : PhysicalPotentialLevel m I0) : transverseEigenvalue s.triangle ≠ 1 := by
  intro hell
  obtain ⟨κ,hκ,hshape,hS⟩ := s.euler_nonisotropic hm hphysical
  have hM : (m 0 : ℂ)+m 1+m 2 ≠ 0 := by
    exact_mod_cast ne_of_gt (add_pos (add_pos (hm 0) (hm 1)) (hm 2))
  have hcube := equal_cube_of_transverse_one s.triangle
    (fun i => Complex.ofReal_ne_zero.mpr (ne_of_gt (hm (i.castLE (by decide))))) hM hS hell
  exact s.false_of_equal_cube hm hphysical hcube

end CentralConfigurations.FiveBody.D2
