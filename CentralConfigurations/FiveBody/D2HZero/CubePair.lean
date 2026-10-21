import CentralConfigurations.FiveBody.D2HZero.CombinationGeometry

namespace CentralConfigurations.FiveBody.D2.HZero
open EllZero
set_option maxHeartbeats 3000000

theorem binary_sign_equal_pair (ε : Fin 3 → ℂ) (hε : ∀ i, ε i=1 ∨ ε i=-1) :
    ∃ i j : Fin 3, i ≠ j ∧ ε i=ε j := by
  classical
  by_cases h01 : ε 0=ε 1
  · exact ⟨0,1,by decide,h01⟩
  by_cases h02 : ε 0=ε 2
  · exact ⟨0,2,by decide,h02⟩
  refine ⟨1,2,by decide,?_⟩
  rcases hε 0 with h0 | h0 <;> rcases hε 1 with h1 | h1 <;> rcases hε 2 with h2 | h2 <;> simp_all

theorem cube_of_metric_multiple {K U w u f : ℂ}
    (hform : K*w=u*f) (hmetric : u^2*(-(U*w))=1) : K^2*U*w^3= -f^2 := by
  have hs := congrArg (fun z : ℂ => z^2) hform
  linear_combination U*w*hs-f^2*hmetric

theorem exists_cube_equal_pair_of_cross_multiple {m : Fin 5 → ℝ}
    (s : FiveBodySource18Certificate m) (hm : ∀ i, 0 < m i)
    {K : ℂ} (hK : ∀ i, crossCombination s i=K*s.triangle.w i) :
    ∃ i j : Fin 3, i ≠ j ∧ s.triangle.w i^3=s.triangle.w j^3 := by
  obtain ⟨ρ,_,_,ε,hε,he⟩ := exists_cross_signs (hm 3) (hm 4) (s.pairZ_ne_zero 0)
    s.w_ne_zero s.pair_balance (s.cross_square 0) (s.cross_square 1)
  obtain ⟨i,j,hij,heq⟩ := binary_sign_equal_pair ε hε
  have hform (k : Fin 3) : K*s.triangle.w k=s.cross 0 k*
      ((m 3 : ℂ)+Complex.I*(m 4 : ℂ)*(ρ : ℂ)*ε k) := by
    rw [← hK k]
    dsimp [crossCombination]
    rw [he k]
    ring
  have hi := cube_of_metric_multiple (hform i) (s.cross_square 0 i)
  have hj := cube_of_metric_multiple (hform j) (s.cross_square 0 j)
  rw [heq] at hi
  refine ⟨i,j,hij,?_⟩
  apply mul_left_cancel₀ (mul_ne_zero (pow_ne_zero 2 (cross_multiple_nonzero s hm hK))
    (s.pairZ_ne_zero 0))
  linear_combination hi-hj

theorem primitive_ratio {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ a) (hcube : a^3=b^3) :
    ∃ h : ℂ, h^2+3=0 ∧ b/a=(h-1)/2 ∧ b/a ≠ 1 := by
  let ω := b/a
  have hω3 : ω^3=1 := by
    dsimp [ω]
    field_simp [ha]
    exact hcube.symm
  have hω1 : ω ≠ 1 := by
    intro h
    apply hb
    have he := (div_eq_iff ha).mp h
    simpa using he
  have hquad : ω^2+ω+1=0 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hω1)
    linear_combination hω3
  let h := 2*ω+1
  refine ⟨h,?_,?_,hω1⟩
  · dsimp [h]
    linear_combination 4*hquad
  · dsimp [h,ω]
    ring

end CentralConfigurations.FiveBody.D2.HZero
