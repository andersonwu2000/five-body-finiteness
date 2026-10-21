import CentralConfigurations.Diagrams.DoubleTriangles

/-!
# Orders of the three separations in a triangle

Chang (2023), Theorem 2.6, the order-comparability part of Rule 2e.
The proof uses a quantitative real inequality, rather than assuming that
arbitrary separation ratios have limits along the given sequence.
-/

namespace CentralConfigurations

open Filter Asymptotics

theorem cube_add_le_four (u v : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) :
    (u + v) ^ 3 ≤ 4 * (u ^ 3 + v ^ 3) := by
  nlinarith [mul_nonneg (sq_nonneg (u - v)) (add_nonneg hu hv)]

/-- The two triangle inequalities turn comparison of x*u^3 and y*v^3
into comparison of x and y. The uniform constant need not be sharp. -/
theorem triangle_product_bound (x y z u v w C : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hu : 0 ≤ u) (hv : 0 < v) (hw : 0 ≤ w)
    (hC : 1 ≤ C) (htriX : x ≤ y + z) (htriV : v ≤ u + w)
    (h₁ : x * u ^ 3 ≤ C * y * v ^ 3)
    (h₃ : z * w ^ 3 ≤ C * y * v ^ 3) : x ≤ 12 * C * y := by
  by_cases hxy : x ≤ 2 * y
  · exact hxy.trans (mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ 12 * C) hy)
  · have hxz : x ≤ 2 * z := by linarith
    have hc : v ^ 3 ≤ 4 * (u ^ 3 + w ^ 3) :=
      (pow_le_pow_left₀ hv.le htriV 3).trans (cube_add_le_four u w hu hw)
    have hxc := mul_le_mul_of_nonneg_left hc hx
    have hxw := mul_le_mul_of_nonneg_right hxz (pow_nonneg hw 3)
    have hbound : x * v ^ 3 ≤ (12 * C * y) * v ^ 3 := by
      nlinarith only [hxc, hxw, h₁, h₃]
    exact le_of_mul_le_mul_right hbound (pow_pos hv 3)

theorem bigO_of_triangle_products {x y z u v w : ℕ → ℂ}
    (hv : ∀ t, v t ≠ 0)
    (htriX : ∀ t, ‖x t‖ ≤ ‖y t‖ + ‖z t‖)
    (htriV : ∀ t, ‖v t‖ ≤ ‖u t‖ + ‖w t‖)
    (h₁ : (fun t => x t * u t ^ 3) =O[atTop] (fun t => y t * v t ^ 3))
    (h₃ : (fun t => z t * w t ^ 3) =O[atTop] (fun t => y t * v t ^ 3)) :
    x =O[atTop] y := by
  obtain ⟨C₁, hC₁, h₁⟩ := h₁.exists_pos
  obtain ⟨C₃, hC₃, h₃⟩ := h₃.exists_pos
  let C := 1 + C₁ + C₃
  have hC : 1 ≤ C := by dsimp [C]; linarith
  have hC₁' : C₁ ≤ C := by dsimp [C]; linarith
  have hC₃' : C₃ ≤ C := by dsimp [C]; linarith
  apply IsBigO.of_bound (12 * C)
  filter_upwards [(h₁.weaken hC₁').bound, (h₃.weaken hC₃').bound] with t ht₁ ht₃
  simp only [norm_mul, norm_pow] at ht₁ ht₃
  apply triangle_product_bound ‖x t‖ ‖y t‖ ‖z t‖ ‖u t‖ ‖v t‖ ‖w t‖ C
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_pos_iff.mpr (hv t))
    (norm_nonneg _) hC (htriX t) (htriV t)
  · simpa only [mul_assoc] using ht₁
  · simpa only [mul_assoc] using ht₃

namespace PairEstimateData

variable (p : PairEstimateData)

theorem z_mul_w_cube (t : ℕ) : p.z t * p.w t ^ 3 = (p.zForce t)⁻¹ ^ 2 := by
  apply mul_left_cancel₀ (pow_ne_zero 2 (p.zForce_ne_zero t))
  calc
    _ = (p.delta t ^ 2 * (p.z t * p.w t)) ^ 3 := by dsimp [zForce]; ring
    _ = 1 := by rw [p.distance_eq]; ring
    _ = _ := by simp [p.zForce_ne_zero t]

theorem stroke_product_order (hz : p.zForce =Θ[atTop] p.scale) :
    (fun t => p.z t * p.w t ^ 3) =Θ[atTop] (fun t => p.eps t ^ 4) :=
  theta_congr_pointwise (hz.inv.pow 2) (fun t => (p.z_mul_w_cube t).symm)
    (fun t => by dsimp [scale]; simp only [inv_pow, inv_inv]; ring)

theorem w_theta_of_z (r : PairEstimateData)
    (hforce : p.zForce =Θ[atTop] r.zForce) (hz : p.z =Θ[atTop] r.z) :
    p.w =Θ[atTop] r.w := by
  have hcube : (fun t => (p.w t)⁻¹ ^ 3) =Θ[atTop] (fun t => (r.w t)⁻¹ ^ 3) :=
    theta_congr_pointwise ((hforce.pow 2).mul hz)
      (fun t => (p.swap.inv_z_cube t).symm) (fun t => (r.swap.inv_z_cube t).symm)
  simpa only [inv_inv] using (theta_of_powers (by decide : (3 : ℕ) ≠ 0) hcube).inv

/-- Upper bounds for both separations reverse the comparison of force terms.
This is the quantitative closure mechanism used in Rule 2f. -/
theorem force_reverse_bound (r : PairEstimateData)
    (hz : p.z =O[atTop] r.z) (hw : p.w =O[atTop] r.w) :
    r.zForce =O[atTop] p.zForce := by
  have hsq : (fun t => (p.zForce t)⁻¹ ^ 2) =O[atTop]
      (fun t => (r.zForce t)⁻¹ ^ 2) :=
    (hz.mul (hw.pow 3)).congr (fun t => p.z_mul_w_cube t) (fun t => r.z_mul_w_cube t)
  have hi : (fun t => (p.zForce t)⁻¹) =O[atTop] (fun t => (r.zForce t)⁻¹) :=
    IsBigO.of_pow (by decide : (2 : ℕ) ≠ 0) hsq
  simpa only [inv_inv] using hi.inv_rev
    (Eventually.of_forall fun t h => (inv_ne_zero (p.zForce_ne_zero t) h).elim)

theorem not_mixed_small (hz : p.z =O[atTop] p.eps) (hw : p.w =o[atTop] p.eps) : False := by
  have hf := p.small_separations_iff_double.mp ⟨hz, hw.isBigO⟩
  exact hw.not_isBigO (Eventually.of_forall p.w_ne_zero).frequently
    (p.swap.stroke_z_lower hf.2)

end PairEstimateData

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem triangle_z_bigO (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hz₁ : l.z.force i j ≠ 0) (hz₂ : l.z.force j k ≠ 0) (hz₃ : l.z.force i k ≠ 0) :
    (fun t => (q t).z i - (q t).z j) =O[atTop] (fun t => (q t).z j - (q t).z k) := by
  let p₁ := ZWSystem.pairEstimateData q hb i j hij
  let p₂ := ZWSystem.pairEstimateData q hb j k hjk
  let p₃ := ZWSystem.pairEstimateData q hb i k hik
  have h₁ := p₁.stroke_product_order ((l.pair_z_stroke_iff hb i j hij).mpr hz₁)
  have h₂ := p₂.stroke_product_order ((l.pair_z_stroke_iff hb j k hjk).mpr hz₂)
  have h₃ := p₃.stroke_product_order ((l.pair_z_stroke_iff hb i k hik).mpr hz₃)
  apply bigO_of_triangle_products (x := p₁.z) (y := p₂.z) (z := p₃.z)
    (u := p₁.w) (v := p₂.w) (w := p₃.w) p₂.w_ne_zero
    (h₁ := (h₁.trans h₂.symm).1) (h₃ := (h₃.trans h₂.symm).1)
  · intro t
    change ‖(q t).z i - (q t).z j‖ ≤ ‖(q t).z j - (q t).z k‖ + ‖(q t).z i - (q t).z k‖
    calc
      _ = ‖((q t).z i - (q t).z k) - ((q t).z j - (q t).z k)‖ := by congr 1; ring
      _ ≤ ‖(q t).z i - (q t).z k‖ + ‖(q t).z j - (q t).z k‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  · intro t
    change ‖(q t).w j - (q t).w k‖ ≤ ‖(q t).w i - (q t).w j‖ + ‖(q t).w i - (q t).w k‖
    calc
      _ = ‖((q t).w i - (q t).w k) - ((q t).w i - (q t).w j)‖ := by congr 1; ring
      _ ≤ ‖(q t).w i - (q t).w k‖ + ‖(q t).w i - (q t).w j‖ := norm_sub_le _ _
      _ = _ := add_comm _ _

theorem z_triangle_orders (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hz₁ : l.z.force i j ≠ 0) (hz₂ : l.z.force j k ≠ 0) (hz₃ : l.z.force i k ≠ 0) :
    ((fun t => (q t).z i - (q t).z j) =Θ[atTop] (fun t => (q t).z j - (q t).z k)) ∧
    ((fun t => (q t).z i - (q t).z j) =Θ[atTop] (fun t => (q t).z i - (q t).z k)) ∧
    ((fun t => (q t).w i - (q t).w j) =Θ[atTop] (fun t => (q t).w j - (q t).w k)) ∧
    ((fun t => (q t).w i - (q t).w j) =Θ[atTop] (fun t => (q t).w i - (q t).w k)) := by
  have hz₁' : l.z.force j i ≠ 0 := by rw [l.z.antisymm j i]; exact neg_ne_zero.mpr hz₁
  have hz₂' : l.z.force k j ≠ 0 := by rw [l.z.antisymm k j]; exact neg_ne_zero.mpr hz₂
  have hz₃' : l.z.force k i ≠ 0 := by rw [l.z.antisymm k i]; exact neg_ne_zero.mpr hz₃
  have h₁₂ : (fun t => (q t).z i - (q t).z j) =Θ[atTop]
      (fun t => (q t).z j - (q t).z k) := by
    refine ⟨l.triangle_z_bigO hb i j k hij hjk hik hz₁ hz₂ hz₃, ?_⟩
    simpa only [isBigO_iff, norm_sub_rev] using
      l.triangle_z_bigO hb k j i (Ne.symm hjk) (Ne.symm hij) (Ne.symm hik) hz₂' hz₁' hz₃'
  have h₁₃ : (fun t => (q t).z i - (q t).z j) =Θ[atTop]
      (fun t => (q t).z i - (q t).z k) := by
    constructor
    · simpa only [isBigO_iff, norm_sub_rev] using
        l.triangle_z_bigO hb j i k (Ne.symm hij) hik hjk hz₁' hz₃ hz₂
    · simpa only [isBigO_iff, norm_sub_rev] using
        l.triangle_z_bigO hb k i j (Ne.symm hik) hij (Ne.symm hjk) hz₃' hz₁ hz₂'
  let p₁ := ZWSystem.pairEstimateData q hb i j hij
  let p₂ := ZWSystem.pairEstimateData q hb j k hjk
  let p₃ := ZWSystem.pairEstimateData q hb i k hik
  have hf₁ := (l.pair_z_stroke_iff hb i j hij).mpr hz₁
  have hf₂ := (l.pair_z_stroke_iff hb j k hjk).mpr hz₂
  have hf₃ := (l.pair_z_stroke_iff hb i k hik).mpr hz₃
  exact ⟨h₁₂, h₁₃, p₁.w_theta_of_z p₂ (hf₁.trans hf₂.symm) h₁₂,
    p₁.w_theta_of_z p₃ (hf₁.trans hf₃.symm) h₁₃⟩

/-- The order-comparability conclusion of Rule 2e for every actual triangle.
Together with `triangle_edge_types`, this gives the full rule. -/
theorem triangle_separation_orders (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (he₁ : l.z.force i j ≠ 0 ∨ l.w.force i j ≠ 0)
    (he₂ : l.z.force j k ≠ 0 ∨ l.w.force j k ≠ 0)
    (he₃ : l.z.force i k ≠ 0 ∨ l.w.force i k ≠ 0) :
    ((fun t => (q t).z i - (q t).z j) =Θ[atTop] (fun t => (q t).z j - (q t).z k)) ∧
    ((fun t => (q t).z i - (q t).z j) =Θ[atTop] (fun t => (q t).z i - (q t).z k)) ∧
    ((fun t => (q t).w i - (q t).w j) =Θ[atTop] (fun t => (q t).w j - (q t).w k)) ∧
    ((fun t => (q t).w i - (q t).w j) =Θ[atTop] (fun t => (q t).w i - (q t).w k)) := by
  rcases l.triangle_edge_types hb i j k hij hjk hik he₁ he₂ he₃ with h | h | h
  · exact l.z_triangle_orders hb i j k hij hjk hik h.1 h.2.1 h.2.2.1
  · have h' := (l.swapBalanced hb).z_triangle_orders (fun t => (hb t).symm)
      i j k hij hjk hik h.1 h.2.1 h.2.2.1
    exact ⟨h'.2.2.1, h'.2.2.2, h'.1, h'.2.1⟩
  · exact l.z_triangle_orders hb i j k hij hjk hik h.1 h.2.1 h.2.2.1

end ScaledZWLimit
end CentralConfigurations
