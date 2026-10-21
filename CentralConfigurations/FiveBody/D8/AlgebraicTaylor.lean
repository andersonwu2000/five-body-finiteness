import CentralConfigurations.FiveBody.D8.UpperChart
import CentralConfigurations.FiveBody.D6Butterfly.WingOrders

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology

/-- The metric equation itself gives the local inverse-square-root expansion.
The sequence may approach the reference point at arbitrary rates. -/
theorem inverse_cube_linearization {f e σ : ℕ → ℂ}
    (hσ : Tendsto σ atTop (𝓝 0)) (he : e =O[atTop] σ)
    (hf : Tendsto f atTop (𝓝 1)) (hm : ∀ n, f n^2*(1+e n)=1) :
    (fun n => f n-1) =O[atTop] σ ∧
    (fun n => f n^3-1+(3/2:ℂ)*e n) =O[atTop] (fun n => σ n^2) := by
  have hf2 := (hf.pow 2).isBigO_one ℂ
  have hi : (fun n => (f n+1)⁻¹) =O[atTop] (fun _ => (1:ℂ)) :=
    ((hf.add_const 1).inv₀ (by norm_num)).isBigO_one ℂ
  have hne : ∀ᶠ n in atTop, f n+1≠0 := (hf.add_const 1).eventually_ne (by norm_num)
  have hd : (fun n => f n-1) =O[atTop] σ := by
    apply ((D6.order_mul_bounded (D6.order_mul_bounded he hf2) hi).neg_left).congr' ?_
      (Filter.Eventually.of_forall (fun _ => rfl))
    filter_upwards [hne] with n hn
    field_simp [hn]
    linear_combination -(hm n)
  refine ⟨hd,?_⟩
  have hvb := ((hf.sub_const 1)).isBigO_one ℂ
  have heb := (he.trans_tendsto hσ).isBigO_one ℂ
  have hvv := hd.pow 2
  have hve : (fun n => (f n-1)*e n) =O[atTop] (fun n => σ n^2) := by simpa only [pow_two] using hd.mul he
  have h := (((((hvv.add (hve.const_mul_left 2)).add
      (D6.order_mul_bounded hvv heb)).const_mul_left (-(3:ℂ)/2)).add
      (hvv.const_mul_left 3))).add (D6.order_mul_bounded hvv hvb)
  apply h.congr_left
  intro n
  dsimp
  linear_combination -(3/2:ℂ)*(hm n)

theorem metric_product_linearization {x y f σ : ℕ → ℂ} {a b : ℂ}
    (ha : a≠0) (hb : b≠0) (hσ : Tendsto σ atTop (𝓝 0))
    (hx : x =O[atTop] σ) (hy : y =O[atTop] σ)
    (hf : Tendsto f atTop (𝓝 1))
    (hm : ∀ n, f n^2*(1+x n/a)*(1+y n/b)=1) :
    (fun n => f n-1) =O[atTop] σ ∧
    (fun n => f n^3-1+(3/2:ℂ)*(x n/a+y n/b)) =O[atTop] (fun n => σ n^2) := by
  have hxy : (fun n => x n*y n/(a*b)) =O[atTop] (fun n => σ n^2) := by
    have h := (hx.mul hy).const_mul_left (a*b)⁻¹
    simpa only [pow_two,div_eq_mul_inv,mul_comm] using h
  have hxy' : (fun n => x n*y n/(a*b)) =O[atTop] σ := by
    apply hxy.trans
    simpa only [mul_one,pow_two] using (isBigO_refl σ atTop).mul (hσ.isBigO_one ℂ)
  have haX : (fun n => x n/a) =O[atTop] σ := by simpa only [div_eq_mul_inv,mul_comm] using hx.const_mul_left a⁻¹
  have hbY : (fun n => y n/b) =O[atTop] σ := by simpa only [div_eq_mul_inv,mul_comm] using hy.const_mul_left b⁻¹
  obtain ⟨hd,hE⟩ := inverse_cube_linearization hσ ((haX.add hbY).add hxy') hf (fun n => by
    have h := hm n
    field_simp [ha,hb] at h ⊢
    linear_combination h)
  refine ⟨hd,?_⟩
  exact (hE.sub (hxy.const_mul_left (3/2:ℂ))).congr_left (fun n => by ring)

theorem root_cube_difference_order {f σ : ℕ → ℂ}
    (hf : Tendsto f atTop (𝓝 1)) (hd : (fun n => f n-1) =O[atTop] σ) :
    (fun n => f n^3-1) =O[atTop] σ := by
  have hb := (((hf.pow 2).add hf).add_const 1).isBigO_one ℂ
  exact (D6.order_mul_bounded hd hb).congr_left (fun n => by ring)

/-- The two rows used by the D8 transverse response, including the shared
nonzero constant in the w row. -/
theorem force_row_linearization {x y f σ : ℕ → ℂ} {a b : ℂ}
    (ha : a≠0) (hb : b≠0) (hσ : Tendsto σ atTop (𝓝 0))
    (hx : x =O[atTop] σ) (hy : y =O[atTop] σ)
    (hf : Tendsto f atTop (𝓝 1))
    (hm : ∀ n, f n^2*(1+x n/a)*(1+y n/b)=1) :
    (fun n => a-(a+x n)*f n^3-(x n/2+3*a/(2*b)*y n)) =O[atTop] (fun n => σ n^2) ∧
    (fun n => a-(b+y n)*f n^3-(a-b)-(3*b/(2*a)*x n+y n/2)) =O[atTop] (fun n => σ n^2) := by
  obtain ⟨hd,hE⟩ := metric_product_linearization ha hb hσ hx hy hf hm
  have hD := root_cube_difference_order hf hd
  constructor
  · have hxd : (fun n => x n*(f n^3-1)) =O[atTop] (fun n => σ n^2) := by simpa only [pow_two] using hx.mul hD
    have he := (hE.const_mul_left (-a)).sub hxd
    apply he.congr_left
    intro n
    field_simp [ha,hb]
    ring
  · have hyd : (fun n => y n*(f n^3-1)) =O[atTop] (fun n => σ n^2) := by simpa only [pow_two] using hy.mul hD
    have he := (hE.const_mul_left (-b)).sub hyd
    apply he.congr_left
    intro n
    field_simp [ha,hb]
    ring

end CentralConfigurations.FiveBody.D8
