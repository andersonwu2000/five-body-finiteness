import CentralConfigurations.FiveBody.D2HZero.Response

namespace CentralConfigurations.FiveBody.D2.HZero
open EllZero
set_option maxHeartbeats 3000000

theorem pair_factor_norm (p q ρ : ℝ) {ε : ℂ} (hε : ε=1 ∨ ε=-1) :
    ‖(p : ℂ)+Complex.I*(q : ℂ)*(ρ : ℂ)*ε‖^2 = p^2+q^2*ρ^2 := by
  rcases hε with rfl | rfl <;>
    rw [← Complex.normSq_eq_norm_sq] <;>
    simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,pow_two] <;> ring

theorem pair_factor_ne_zero {p q ρ : ℝ} (hp : 0 < p) {ε : ℂ} (hε : ε=1 ∨ ε=-1) :
    (p : ℂ)+Complex.I*(q : ℂ)*(ρ : ℂ)*ε ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  rcases hε with rfl | rfl <;> simp [Complex.mul_re,Complex.mul_im] at hr <;> linarith

theorem combination_norm {p q ρ : ℝ} {u v ε : ℂ}
    (hε : ε=1 ∨ ε=-1) (hv : v=Complex.I*(ρ : ℂ)*ε*u) :
    ‖(p : ℂ)*u+(q : ℂ)*v‖^2=‖u‖^2*(p^2+q^2*ρ^2) := by
  have hf : (p : ℂ)*u+(q : ℂ)*v = u*((p : ℂ)+Complex.I*(q : ℂ)*(ρ : ℂ)*ε) := by
    rw [hv]; ring
  rw [hf,norm_mul,mul_pow,pair_factor_norm p q ρ hε]

theorem combination_ne_zero {p q ρ : ℝ} (hp : 0 < p) {u v ε : ℂ}
    (hu : u ≠ 0) (hε : ε=1 ∨ ε=-1) (hv : v=Complex.I*(ρ : ℂ)*ε*u) :
    (p : ℂ)*u+(q : ℂ)*v ≠ 0 := by
  have hf : (p : ℂ)*u+(q : ℂ)*v = u*((p : ℂ)+Complex.I*(q : ℂ)*(ρ : ℂ)*ε) := by
    rw [hv]; ring
  rw [hf]
  exact mul_ne_zero hu (pair_factor_ne_zero hp hε)

theorem cross_multiple_nonzero {m : Fin 5 → ℝ} (s : FiveBodySource18Certificate m)
    (hm : ∀ i, 0 < m i) {K : ℂ} (hK : ∀ i, crossCombination s i=K*s.triangle.w i) : K ≠ 0 := by
  obtain ⟨ρ,_,_,ε,hε,he⟩ := exists_cross_signs (hm 3) (hm 4) (s.pairZ_ne_zero 0)
    s.w_ne_zero s.pair_balance (s.cross_square 0) (s.cross_square 1)
  have hn := combination_ne_zero (q := m 4) (hm 3) (root_ne_zero (s.cross_square 0 0)) (hε 0) (he 0)
  intro hzero
  apply hn
  change crossCombination s 0=0
  rw [hK 0,hzero,zero_mul]

theorem equal_norms_of_cross_multiple {m : Fin 5 → ℝ} (s : FiveBodySource18Certificate m)
    (hm : ∀ i, 0 < m i) {K : ℂ} (hK : ∀ i, crossCombination s i=K*s.triangle.w i) :
    ∀ i j, ‖s.triangle.w i‖=‖s.triangle.w j‖ := by
  obtain ⟨ρ,_,_,ε,hε,he⟩ := exists_cross_signs (hm 3) (hm 4) (s.pairZ_ne_zero 0)
    s.w_ne_zero s.pair_balance (s.cross_square 0) (s.cross_square 1)
  let F : ℝ := m 3^2+m 4^2*ρ^2
  have hn (i : Fin 3) : ‖K‖^2*‖s.triangle.w i‖^2=‖s.cross 0 i‖^2*F := by
    have h := combination_norm (p := m 3) (q := m 4) (hε i) (he i)
    change ‖crossCombination s i‖^2=‖s.cross 0 i‖^2*F at h
    rw [hK i,norm_mul,mul_pow] at h
    exact h
  have hcube (i : Fin 3) : ‖K‖^2*‖s.pairZ 0‖*‖s.triangle.w i‖^3=F := by
    have hr := root_norm_equation (s.cross_square 0 i)
    linear_combination ‖s.pairZ 0‖*‖s.triangle.w i‖*hn i+F*hr
  intro i j
  apply (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) (by decide : (3 : ℕ) ≠ 0)).mp
  apply mul_left_cancel₀ (mul_ne_zero
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr (cross_multiple_nonzero s hm hK)))
    (norm_ne_zero_iff.mpr (s.pairZ_ne_zero 0)))
  linear_combination hcube i-hcube j

end CentralConfigurations.FiveBody.D2.HZero
