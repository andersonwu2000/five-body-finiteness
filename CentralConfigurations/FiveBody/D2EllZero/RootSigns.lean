import CentralConfigurations.FiveBody.D2Exceptional.TorqueDisk
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace CentralConfigurations.FiveBody.D2.EllZero
set_option maxHeartbeats 2000000

theorem second_root_square {p q : ℝ} {U V w u v : ℂ}
    (_hp : 0 < p) (hU : U ≠ 0) (hw : w ≠ 0)
    (hbalance : (p : ℂ)*U+(q : ℂ)*V=0)
    (hu : u^2*(-(U*w))=1) (hv : v^2*(-(V*w))=1) :
    (p : ℂ)*v^2+(q : ℂ)*u^2=0 := by
  apply mul_left_cancel₀ (mul_ne_zero hU hw)
  linear_combination w*v^2*hbalance+(q : ℂ)*hv-(q : ℂ)*hu

/-- Both pair-root rows are represented together; each original root's sign remains free. -/
theorem exists_cross_signs {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    {U V : ℂ} (hU : U ≠ 0) {w u v : Fin 3 → ℂ} (hw : ∀ i, w i ≠ 0)
    (hbalance : (p : ℂ)*U+(q : ℂ)*V=0)
    (hu : ∀ i, u i^2*(-(U*w i))=1) (hv : ∀ i, v i^2*(-(V*w i))=1) :
    ∃ ρ : ℝ, 0 < ρ ∧ p*ρ^2=q ∧
      ∃ ε : Fin 3 → ℂ, (∀ i, ε i=1 ∨ ε i=-1) ∧
        ∀ i, v i=Complex.I*(ρ : ℂ)*ε i*u i := by
  classical
  let ρ := Real.sqrt (q/p)
  have hρ : 0 < ρ := Real.sqrt_pos.mpr (div_pos hq hp)
  have hρsq : p*ρ^2=q := by
    dsimp [ρ]
    rw [Real.sq_sqrt (le_of_lt (div_pos hq hp)),mul_div_cancel₀ _ (ne_of_gt hp)]
  have hρC : (p : ℂ)*(ρ : ℂ)^2=(q : ℂ) := by exact_mod_cast hρsq
  have hsign (i : Fin 3) : ∃ ε : ℂ, (ε=1 ∨ ε=-1) ∧
      v i=Complex.I*(ρ : ℂ)*ε*u i := by
    have hr := second_root_square hp hU (hw i) hbalance (hu i) (hv i)
    have hs : v i^2=(Complex.I*(ρ : ℂ)*u i)^2 := by
      apply mul_left_cancel₀ (by exact_mod_cast (ne_of_gt hp) : (p : ℂ) ≠ 0)
      have hI : Complex.I^2+1=0 := by simp
      linear_combination hr+u i^2*hρC-(p : ℂ)*(ρ : ℂ)^2*u i^2*hI
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
    · exact ⟨1,Or.inl rfl,by simpa using he⟩
    · exact ⟨-1,Or.inr rfl,by simpa using he⟩
  choose ε hε he using hsign
  exact ⟨ρ,hρ,hρsq,ε,hε,he⟩

end CentralConfigurations.FiveBody.D2.EllZero
