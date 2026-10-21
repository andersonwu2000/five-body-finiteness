import CentralConfigurations.FiveBody.D2Actual.Energy

/-!
# Euler geometry of the extracted D2 triangle

The energy exclusions imply that the limiting triangle is Euler and
nonisotropic. The regular implicit-function argument and exceptional-stratum
exclusions are developed in the corresponding D2 modules.
-/
namespace CentralConfigurations.FiveBody.D2
open scoped BigOperators

theorem zw_potential {n : ℕ} {mass : Fin n → ℂ} (q : ZWSystem ℂ n mass) :
    q.toNormalized.potential = ∑ i, mass i*q.z i*q.w i := by
  rw [q.toNormalized.potential_eq_inertia]
  unfold NormalizedSystem.inertia
  apply Finset.sum_congr rfl
  intro i _
  have h := inverse_zw_separation (q.z i) (q.w i) 0 0
  simp only [add_zero, sub_zero, mul_zero, zero_div] at h
  change mass i*(((q.z i+q.w i)/2)^2+(Complex.I*(q.w i-q.z i)/2)^2) = _
  rw [h]
  ring

theorem proportional_of_area_zero {mass : Fin 3 → ℂ}
    (r : ZWSystem ℂ 3 mass) (harea : threeBodyArea r = 0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ ∀ i, r.z i = κ*r.w i := by
  let κ : ℂ := (r.z 0-r.z 1)/(r.w 0-r.w 1)
  have hwne := r.w_separation_ne_zero (by decide : (0 : Fin 3) ≠ 1)
  have hκ : κ ≠ 0 := div_ne_zero
    (r.z_separation_ne_zero (by decide : (0 : Fin 3) ≠ 1)) hwne
  have h01 : r.z 0-r.z 1 = κ*(r.w 0-r.w 1) := (div_mul_cancel₀ _ hwne).symm
  have h12 : r.z 1-r.z 2 = κ*(r.w 1-r.w 2) := by
    dsimp [κ]
    field_simp [hwne]
    dsimp [threeBodyArea] at harea
    linear_combination -harea
  have h0 : r.z 0 = κ*r.w 0 := by
    have hz := r.force_z 0
    have hw := r.force_w 0
    simp [Fin.sum_univ_succ] at hz hw
    linear_combination hz-κ*hw + (mass 1*r.delta 0 1^3+mass 2*r.delta 0 2^3)*h01 +
      mass 2*r.delta 0 2^3*h12
  have h1 : r.z 1 = κ*r.w 1 := by linear_combination h0-h01
  have h2 : r.z 2 = κ*r.w 2 := by linear_combination h1-h12
  exact ⟨κ,hκ,fun i => by fin_cases i <;> assumption⟩

theorem potential_of_proportional {mass : Fin 3 → ℂ} (r : ZWSystem ℂ 3 mass)
    {κ : ℂ} (hκ : ∀ i, r.z i = κ*r.w i) :
    r.toNormalized.potential = κ*(∑ i, mass i*r.w i^2) := by
  rw [zw_potential, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [hκ i]
  ring

theorem ActualLimit.euler_nonisotropic {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
    (s : ActualLimit m q l (I0 : ℂ)) (hm : ∀ i, 0 < m i)
    (hphysical : PhysicalPotentialLevel m I0) :
    ∃ κ : ℂ, κ ≠ 0 ∧ (∀ i, s.triangle.z i = κ*s.triangle.w i) ∧
      (∑ i : Fin 3, (m (i.castLE (by decide)) : ℂ)*s.triangle.w i^2) ≠ 0 := by
  obtain ⟨κ,hκ,hshape⟩ := proportional_of_area_zero s.triangle
    (s.triangle_area_zero hm hphysical)
  refine ⟨κ,hκ,hshape,?_⟩
  intro hS
  have hQ := potential_of_proportional s.triangle hshape
  rw [hS, mul_zero] at hQ
  exact s.false_of_triangle_potential_zero hm hphysical hQ

end CentralConfigurations.FiveBody.D2
