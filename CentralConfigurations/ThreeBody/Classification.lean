import CentralConfigurations.Model.ZWMassCenter
import Mathlib.Tactic

/-!
# Complex three-body Euler/Lagrange coverage

Albouy--Kaloshin, Appendix, equations (44)--(48). The alternatives are
not claimed disjoint: complex collinear Lagrange configurations exist.
Every equation here follows from the original ZW force and distance rows.
-/

namespace CentralConfigurations
open scoped BigOperators

def threeBodyArea {mass : Fin 3 → ℂ} (q : ZWSystem ℂ 3 mass) : ℂ :=
  (q.z 0-q.z 1)*(q.w 1-q.w 2) - (q.z 1-q.z 2)*(q.w 0-q.w 1)

namespace ZWSystem
variable {mass : Fin 3 → ℂ} (q : ZWSystem ℂ 3 mass)

theorem three_body_reduced_z_row_zero :
    mass 1*((mass 0+mass 1+mass 2)*q.delta 0 1^3-1)*(q.z 0-q.z 1) +
    mass 2*((mass 0+mass 1+mass 2)*q.delta 0 2^3-1)*(q.z 0-q.z 2) = 0 := by
  have hf := q.force_z 0
  have hc := q.mass_center_z
  simp [Fin.sum_univ_succ] at hf hc
  linear_combination -(mass 0+mass 1+mass 2)*hf + hc

theorem three_body_reduced_z_row_one :
    mass 0*((mass 0+mass 1+mass 2)*q.delta 0 1^3-1)*(q.z 1-q.z 0) +
    mass 2*((mass 0+mass 1+mass 2)*q.delta 1 2^3-1)*(q.z 1-q.z 2) = 0 := by
  have hf := q.force_z 1
  have hc := q.mass_center_z
  simp [Fin.sum_univ_succ, q.delta_symm 1 0] at hf hc
  linear_combination -(mass 0+mass 1+mass 2)*hf + hc

theorem three_body_lagrange_of_area_ne_zero
    (hm : ∀ i, mass i ≠ 0) (hA : threeBodyArea q ≠ 0) :
    ∀ i j, i ≠ j → (mass 0+mass 1+mass 2)*q.delta i j^3 = 1 := by
  have hz := q.three_body_reduced_z_row_zero
  have hw := q.swap.three_body_reduced_z_row_zero
  change mass 1*((mass 0+mass 1+mass 2)*q.delta 0 1^3-1)*(q.w 0-q.w 1) +
    mass 2*((mass 0+mass 1+mass 2)*q.delta 0 2^3-1)*(q.w 0-q.w 2) = 0 at hw
  have h01 : (mass 0+mass 1+mass 2)*q.delta 0 1^3 = 1 := by
    have h : mass 1 * ((mass 0+mass 1+mass 2)*q.delta 0 1^3-1) *
        threeBodyArea q = 0 := by
      dsimp [threeBodyArea]
      linear_combination (q.w 0-q.w 2)*hz - (q.z 0-q.z 2)*hw
    exact sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hA)).resolve_left (hm 1))
  have h02 : (mass 0+mass 1+mass 2)*q.delta 0 2^3 = 1 := by
    have h : mass 2 * ((mass 0+mass 1+mass 2)*q.delta 0 2^3-1) *
        threeBodyArea q = 0 := by
      dsimp [threeBodyArea]
      linear_combination (q.z 0-q.z 1)*hw - (q.w 0-q.w 1)*hz
    exact sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hA)).resolve_left (hm 2))
  have h12 : (mass 0+mass 1+mass 2)*q.delta 1 2^3 = 1 := by
    have h := q.three_body_reduced_z_row_one
    simp only [h01,sub_self,mul_zero,zero_mul,zero_add] at h
    exact sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp h).resolve_right
      (q.z_separation_ne_zero (by decide : (1 : Fin 3) ≠ 2)))).resolve_left (hm 2))
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [q.delta_symm 1 0,q.delta_symm 2 0,q.delta_symm 2 1]

theorem three_body_euler_or_lagrange (hm : ∀ i, mass i ≠ 0) :
    threeBodyArea q = 0 ∨
      ∀ i j, i ≠ j → (mass 0+mass 1+mass 2)*q.delta i j^3 = 1 := by
  by_cases h : threeBodyArea q = 0
  · exact Or.inl h
  · exact Or.inr (q.three_body_lagrange_of_area_ne_zero hm h)

/-- The mass-independent cyclic relation, equation (47). It holds before
specializing to the collinear branch. -/
theorem three_body_cyclic_w_force :
    q.w 0*q.wForce 1 2 + q.w 1*q.wForce 2 0 + q.w 2*q.wForce 0 1 = 0 := by
  have h0 := q.force_w 0
  have h1 := q.force_w 1
  have h2 := q.force_w 2
  simp [Fin.sum_univ_succ,q.delta_symm 1 0,q.delta_symm 2 0,q.delta_symm 2 1] at h0 h1 h2
  dsimp [wForce]
  rw [q.delta_symm 2 0]
  linear_combination q.delta 1 2^3*(q.w 1-q.w 2)*h0 +
    q.delta 0 2^3*(q.w 2-q.w 0)*h1 + q.delta 0 1^3*(q.w 0-q.w 1)*h2

theorem three_body_cyclic_distance_squares_of_area_zero (hA : threeBodyArea q = 0) :
    (q.delta 1 2*(q.w 1-q.w 2))^2 = (q.delta 0 1*(q.w 0-q.w 1))^2 ∧
    (q.delta 2 0*(q.w 2-q.w 0))^2 = (q.delta 0 1*(q.w 0-q.w 1))^2 := by
  dsimp [threeBodyArea] at hA
  let c := (q.z 0-q.z 1)/(q.w 0-q.w 1)
  have hzn := q.z_separation_ne_zero (by decide : (0 : Fin 3) ≠ 1)
  have hwn := q.w_separation_ne_zero (by decide : (0 : Fin 3) ≠ 1)
  have hc : c ≠ 0 := div_ne_zero hzn hwn
  have hz01 : q.z 0-q.z 1 = c*(q.w 0-q.w 1) := (div_mul_cancel₀ _ hwn).symm
  have hz12 : q.z 1-q.z 2 = c*(q.w 1-q.w 2) := by
    dsimp [c]
    field_simp [hwn]
    linear_combination -hA
  have hz20 : q.z 2-q.z 0 = c*(q.w 2-q.w 0) := by
    linear_combination -hz01-hz12
  have h01 : (q.delta 0 1*(q.w 0-q.w 1))^2*c = 1 := by
    have h := q.distance 0 1 (by decide)
    rw [hz01] at h
    linear_combination h
  have h12 : (q.delta 1 2*(q.w 1-q.w 2))^2*c = 1 := by
    have h := q.distance 1 2 (by decide)
    rw [hz12] at h
    linear_combination h
  have h20 : (q.delta 2 0*(q.w 2-q.w 0))^2*c = 1 := by
    have h := q.distance 2 0 (by decide)
    rw [hz20] at h
    linear_combination h
  exact ⟨mul_right_cancel₀ hc (h12.trans h01.symm), mul_right_cancel₀ hc (h20.trans h01.symm)⟩

end ZWSystem
end CentralConfigurations
