import CentralConfigurations.FiveBody.D2Actual.SignedEulerMetric
import CentralConfigurations.FiveBody.D2Actual.TransverseOne

namespace CentralConfigurations.FiveBody.D2.Exceptional

structure GapData {mass : Fin 3 → ℂ} (r : ZWSystem ℂ 3 mass) where
  x : ℂ
  x_ne_zero : x ≠ 0
  x_ne_one : x ≠ 1
  scale : ℂ
  scale_ne_zero : scale ≠ 0
  difference01 : r.w 1-r.w 0 = scale
  difference02 : r.w 2-r.w 0 = scale*x
  phase : ℂ
  phase_ne_zero : phase ≠ 0
  lam : ℂ
  lam_ne_zero : lam ≠ 0
  lam_eq : lam = phase^3
  sign13 : ℂ
  sign23 : ℂ
  sign13_values : sign13=1 ∨ sign13=-1
  sign23_values : sign23=1 ∨ sign23=-1
  cube01 : r.delta 0 1^3 = 1/lam
  cube02 : r.delta 0 2^3 = sign13/(lam*x^3)
  cube12 : r.delta 1 2^3 = sign23/(lam*(x-1)^3)
  trace : transverseEigenvalue r =
    ((mass 0+mass 1)+(mass 0+mass 2)*sign13/x^3+
      (mass 1+mass 2)*sign23/(x-1)^3)/lam-1

theorem cube_of_signed_factor {d θ x σ : ℂ}
    (hθ : θ ≠ 0) (hx : x ≠ 0) (hσ : σ=1 ∨ σ=-1) (hfactor : d*θ*x=σ) :
    d^3=σ/(θ^3*x^3) := by
  have hcube : σ^3=σ := by rcases hσ with rfl | rfl <;> norm_num
  apply (eq_div_iff (mul_ne_zero (pow_ne_zero 3 hθ) (pow_ne_zero 3 hx))).mpr
  rw [← hcube,← hfactor]
  ring

theorem exists_gapData {mass : Fin 3 → ℂ} {r : ZWSystem ℂ 3 mass}
    (s : SignedEulerMetric r) : Nonempty (GapData r) := by
  let g := r.w 1-r.w 0
  have hg : g ≠ 0 := r.w_separation_ne_zero (by decide : (1 : Fin 3) ≠ 0)
  let x := (r.w 2-r.w 0)/g
  have hx : x ≠ 0 := div_ne_zero (r.w_separation_ne_zero (by decide : (2 : Fin 3) ≠ 0)) hg
  have hxg : r.w 2-r.w 0 = g*x := by dsimp [x]; rw [mul_div_cancel₀ _ hg]
  have hx1 : x ≠ 1 := by
    intro he
    have hd : r.w 2-r.w 1 = 0 := by dsimp [g] at hxg; rw [he,mul_one] at hxg; linear_combination hxg
    exact r.w_separation_ne_zero (by decide : (2 : Fin 3) ≠ 1) hd
  let ε := -s.sign 0 1
  have hsign01 := s.sign_values 0 1 (by decide)
  have hε : ε ≠ 0 := by rcases hsign01 with he | he <;> simp [ε,he]
  have hsquare : s.sign 0 1^2 = 1 := by rcases hsign01 with he | he <;> simp [he]
  let θ := ε*s.theta*g
  have hθ : θ ≠ 0 := mul_ne_zero (mul_ne_zero hε s.theta_ne_zero) hg
  let lam := θ^3
  have hlam : lam ≠ 0 := pow_ne_zero 3 hθ
  let σ13 := s.sign 0 1*s.sign 0 2
  let σ23 := s.sign 0 1*s.sign 1 2
  have h13 : σ13=1 ∨ σ13=-1 := by
    rcases hsign01 with h | h <;> rcases s.sign_values 0 2 (by decide) with k | k <;> simp [σ13,h,k]
  have h23 : σ23=1 ∨ σ23=-1 := by
    rcases hsign01 with h | h <;> rcases s.sign_values 1 2 (by decide) with k | k <;> simp [σ23,h,k]
  have hf01 : r.delta 0 1*θ*1=1 := by
    have hf := s.metric_factor 0 1
    dsimp [θ,ε,g]
    linear_combination hsquare-s.sign 0 1*hf
  have hf02 : r.delta 0 2*θ*x=σ13 := by
    have hf := s.metric_factor 0 2
    dsimp [θ,ε,σ13]
    linear_combination -s.sign 0 1*hf+r.delta 0 2*s.sign 0 1*s.theta*hxg
  have hf12 : r.delta 1 2*θ*(x-1)=σ23 := by
    have hf := s.metric_factor 1 2
    dsimp [θ,ε,σ23,g] at ⊢
    dsimp [g] at hxg
    linear_combination -s.sign 0 1*hf+r.delta 1 2*s.sign 0 1*s.theta*hxg
  have hc01 : r.delta 0 1^3=1/lam := by
    simpa only [one_pow,mul_one,lam] using cube_of_signed_factor hθ (by norm_num) (Or.inl rfl) hf01
  have hc02 : r.delta 0 2^3=σ13/(lam*x^3) := cube_of_signed_factor hθ hx h13 hf02
  have hc12 : r.delta 1 2^3=σ23/(lam*(x-1)^3) :=
    cube_of_signed_factor hθ (sub_ne_zero.mpr hx1) h23 hf12
  have ht : transverseEigenvalue r =
      ((mass 0+mass 1)+(mass 0+mass 2)*σ13/x^3+(mass 1+mass 2)*σ23/(x-1)^3)/lam-1 := by
    dsimp [transverseEigenvalue]
    rw [hc01,hc02,hc12]
    field_simp [hlam,hx,sub_ne_zero.mpr hx1]
  exact ⟨{
    x := x, x_ne_zero := hx, x_ne_one := hx1, scale := g, scale_ne_zero := hg,
    difference01 := rfl, difference02 := hxg, phase := θ, phase_ne_zero := hθ,
    lam := lam, lam_ne_zero := hlam, lam_eq := rfl,
    sign13 := σ13, sign23 := σ23, sign13_values := h13, sign23_values := h23,
    cube01 := hc01, cube02 := hc02, cube12 := hc12, trace := ht }⟩

end CentralConfigurations.FiveBody.D2.Exceptional
