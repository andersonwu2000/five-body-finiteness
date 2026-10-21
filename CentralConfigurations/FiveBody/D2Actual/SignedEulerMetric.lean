import CentralConfigurations.FiveBody.D2Actual.EulerResidual
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! Coherent Euler signs derived from the original unsquared metric variables. -/
namespace CentralConfigurations.FiveBody.D2
open scoped BigOperators

structure SignedEulerMetric {mass : Fin 3 → ℂ} (r : ZWSystem ℂ 3 mass) where
  theta : ℂ
  theta_ne_zero : theta ≠ 0
  proportional : ∀ i, r.z i = theta^2*r.w i
  sign : Fin 3 → Fin 3 → ℂ
  sign_diagonal : ∀ i, sign i i = 0
  sign_antisymm : ∀ i j, sign j i = -sign i j
  sign_values : ∀ i j, i ≠ j → sign i j = 1 ∨ sign i j = -1
  metric_factor : ∀ i j, sign i j = r.delta i j*theta*(r.w i-r.w j)
  euler_force : ∀ i, theta^3*r.w i =
    ∑ j, mass j*sign i j/(r.w i-r.w j)^2
  potential : r.toNormalized.potential = theta^2*(∑ i, mass i*r.w i^2)

theorem exists_signedEulerMetric {mass : Fin 3 → ℂ} (r : ZWSystem ℂ 3 mass)
    {κ : ℂ} (hκ : κ ≠ 0) (hshape : ∀ i, r.z i = κ*r.w i) :
    Nonempty (SignedEulerMetric r) := by
  obtain ⟨θ,hθ⟩ := IsAlgClosed.exists_pow_nat_eq κ (by decide : 0 < (2 : ℕ))
  have hθ0 : θ ≠ 0 := by intro he; simp only [he,zero_pow (by decide : 2≠0)] at hθ; exact hκ hθ.symm
  let σ : Fin 3 → Fin 3 → ℂ := fun i j => r.delta i j*θ*(r.w i-r.w j)
  have hsquare (i j : Fin 3) (hij : i ≠ j) : σ i j^2 = 1 := by
    have h := r.distance i j hij
    rw [hshape i,hshape j] at h
    dsimp [σ]
    rw [mul_pow,mul_pow,hθ]
    linear_combination h
  have hcube (i j : Fin 3) : σ i j^3 = σ i j := by
    by_cases hij : i=j
    · subst j; simp [σ]
    · calc
        σ i j^3 = σ i j^2*σ i j := by ring
        _ = σ i j := by rw [hsquare i j hij,one_mul]
  have hterm (i j : Fin 3) : θ^3*r.delta i j^3*(r.w i-r.w j) =
      σ i j/(r.w i-r.w j)^2 := by
    by_cases hij : i=j
    · subst j; simp [σ]
    · have hw := r.w_separation_ne_zero hij
      apply (eq_div_iff (pow_ne_zero 2 hw)).mpr
      have h := hcube i j
      dsimp [σ] at h ⊢
      linear_combination h
  refine ⟨{
    theta := θ, theta_ne_zero := hθ0,
    proportional := fun i => by rw [hθ]; exact hshape i,
    sign := σ, sign_diagonal := fun i => by simp [σ],
    sign_antisymm := fun i j => by dsimp [σ]; rw [r.delta_symm j i]; ring,
    sign_values := ?_, metric_factor := fun _ _ => rfl,
    euler_force := ?_, potential := ?_ }⟩
  · intro i j hij
    have hfactor : (σ i j-1)*(σ i j+1) = 0 := by linear_combination hsquare i j hij
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  · intro i
    conv_lhs => rw [r.force_w i, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [show θ^3*(mass j*r.delta i j^3*(r.w i-r.w j)) =
      mass j*(θ^3*r.delta i j^3*(r.w i-r.w j)) by ring, hterm]
    ring
  · rw [hθ]
    exact potential_of_proportional r hshape

end CentralConfigurations.FiveBody.D2
