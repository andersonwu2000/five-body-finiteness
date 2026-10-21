import CentralConfigurations.FiveBody.D8.AlgebraicTaylor

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology

theorem absorb_quadratic {s g : ℕ → ℝ} (hs : Tendsto s atTop (𝓝 0))
    (hsn : ∀ n, 0≤s n) (hgn : ∀ n, 0≤g n)
    (h : s =O[atTop] (fun n => g n+s n^2)) : s =O[atTop] g := by
  obtain ⟨C,hC,hb⟩ := h.exists_pos
  have he : ∀ᶠ n in atTop, s n<1/(2*C) := (tendsto_order.1 hs).2 _ (by positivity)
  apply isBigO_iff.mpr ⟨2*C,?_⟩
  filter_upwards [hb.bound,he] with n hn hsmall
  simp only [Real.norm_of_nonneg (hsn n),Real.norm_of_nonneg (hgn n),
    Real.norm_of_nonneg (add_nonneg (hgn n) (sq_nonneg _))] at hn ⊢
  have hsc : 2*C*s n<1 := by simpa only [mul_comm] using (lt_div_iff₀ (by positivity : 0<2*C)).mp hsmall
  nlinarith [mul_le_mul_of_nonneg_right hsc.le (hsn n)]

theorem linear_two_response {x y f g γ : ℕ → ℂ} {a b : ℂ} (hab : a-b≠0)
    (hx0 : Tendsto x atTop (𝓝 0)) (hy0 : Tendsto y atTop (𝓝 0))
    (hf : f =O[atTop] γ) (hg : g =O[atTop] γ)
    (hEf : (fun n => f n-(x n/2+a*y n)) =O[atTop] (fun n => ((‖x n‖+‖y n‖:ℝ):ℂ)^2))
    (hEg : (fun n => g n-(x n/2+b*y n)) =O[atTop] (fun n => ((‖x n‖+‖y n‖:ℝ):ℂ)^2)) :
    (fun n => ((‖x n‖+‖y n‖:ℝ):ℂ)) =O[atTop] γ := by
  let s : ℕ → ℝ := fun n => ‖x n‖+‖y n‖
  let G : ℕ → ℝ := fun n => ‖γ n‖+s n^2
  have hnorm n : ‖((‖x n‖+‖y n‖:ℝ):ℂ)‖=‖x n‖+‖y n‖ := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
  have h1 : (fun n => x n/2+a*y n) =O[atTop] G := by
    have h := hf.norm_right.add_add hEf.neg_left.norm_right
    simp only [norm_norm,norm_pow,hnorm,Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at h
    exact h.congr_left (fun n => by ring)
  have h2 : (fun n => x n/2+b*y n) =O[atTop] G := by
    have h := hg.norm_right.add_add hEg.neg_left.norm_right
    simp only [norm_norm,norm_pow,hnorm,Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))] at h
    exact h.congr_left (fun n => by ring)
  have hy : y =O[atTop] G := by
    apply ((h1.sub h2).const_mul_left (a-b)⁻¹).congr_left
    intro n; field_simp [hab]; ring
  have hx : x =O[atTop] G := by
    exact ((h1.sub (hy.const_mul_left a)).const_mul_left 2).congr_left (fun n => by ring)
  have hsn : ∀ n, 0≤s n := fun n => add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hs0 : Tendsto s atTop (𝓝 0) := by simpa only [s,norm_zero,add_zero] using hx0.norm.add hy0.norm
  have hsG : s =O[atTop] G := hx.norm_left.add hy.norm_left
  have hh := absorb_quadratic hs0 hsn (fun n => norm_nonneg (γ n)) hsG
  simpa only [isBigO_iff,Complex.norm_real,Real.norm_eq_abs,norm_norm,s,abs_norm] using hh

theorem linear_one_response {x y f γ : ℕ → ℂ} {a b : ℂ} (hb : b≠0)
    (hx0 : Tendsto x atTop (𝓝 0)) (hy0 : Tendsto y atTop (𝓝 0))
    (hx : x =O[atTop] γ) (hf : f =O[atTop] γ)
    (hE : (fun n => f n-(a*x n+b*y n)) =O[atTop] (fun n => ((‖x n‖+‖y n‖:ℝ):ℂ)^2)) :
    (fun n => ((‖x n‖+‖y n‖:ℝ):ℂ)) =O[atTop] γ := by
  have h2 : (fun n => x n/2) =O[atTop] γ := by
    simpa only [div_eq_mul_inv,mul_comm] using hx.const_mul_left (2:ℂ)⁻¹
  have hf' : (fun n => f n+(1/2-a)*x n) =O[atTop] γ := hf.add (hx.const_mul_left (1/2-a))
  have hE' : (fun n => (f n+(1/2-a)*x n)-(x n/2+b*y n)) =O[atTop]
      (fun n => ((‖x n‖+‖y n‖:ℝ):ℂ)^2) := hE.congr_left (fun n => by ring)
  have hzero : (fun n => x n/2-(x n/2+(0:ℂ)*y n)) =O[atTop]
      (fun n => ((‖x n‖+‖y n‖:ℝ):ℂ)^2) := by simpa using isBigO_zero (fun n => ((‖x n‖+‖y n‖:ℝ):ℂ)^2) atTop
  exact linear_two_response (by simpa using hb) hx0 hy0 hf' h2 hE' hzero

end CentralConfigurations.FiveBody.D8
