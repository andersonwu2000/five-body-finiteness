import CentralConfigurations.FiveBody.D9Maximal
import CentralConfigurations.FiveBody.D9Energy

namespace CentralConfigurations.FiveBody.D9
open Filter Asymptotics
open scoped Topology

theorem zero_of_power {f : ℕ → ℂ} {n : ℕ} (hn : n ≠ 0)
    (h : Tendsto (fun t => f t ^ n) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  have hh : (f ^ n) =o[atTop] ((fun _ => (1 : ℂ)) ^ n) := by
    change (fun t => f t ^ n) =o[atTop] (fun _ => (1 : ℂ)^n)
    simpa only [one_pow] using (isLittleO_one_iff ℂ).2 h
  exact (isLittleO_one_iff ℂ).1 (hh.of_pow hn)

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}

theorem inverse_zero_of_separation_small_force
    (hw : (fun t => (q t).w 0 - (q t).w 3) =o[atTop]
      (fun t => (q t).wForce 0 3)) :
    Tendsto (fun t => ((q t).delta 0 3)⁻¹) atTop (𝓝 0) := by
  apply zero_of_power (n := 3) (by decide)
  convert hw.tendsto_div_nhds_zero using 1
  funext t
  have hd := (q t).toNormalized.delta_ne_zero (by decide : (0 : Fin 5) ≠ 3)
  change (q t).delta 0 3 ≠ 0 at hd
  have hw := (q t).w_separation_ne_zero (by decide : (0 : Fin 5) ≠ 3)
  dsimp [ZWSystem.wForce]
  field_simp

theorem relative_inverse_zero {i a : Fin 5} (hia : i ≠ a)
    (hz : (fun t => (q t).z 0 - (q t).z 3) =o[atTop]
      (fun t => (q t).z i - (q t).z a))
    (hw : (fun t => (q t).w 0 - (q t).w 3) =O[atTop]
      (fun t => (q t).w i - (q t).w a)) :
    Tendsto (fun t => (q t).delta i a / (q t).delta 0 3) atTop (𝓝 0) := by
  apply zero_of_power (n := 2) (by decide)
  convert (hz.mul_isBigO hw).tendsto_div_nhds_zero using 1
  funext t
  have hd := (q t).toNormalized.delta_ne_zero (by decide : (0 : Fin 5) ≠ 3)
  change (q t).delta 0 3 ≠ 0 at hd
  have hz0 := (q t).z_separation_ne_zero hia
  have hw0 := (q t).w_separation_ne_zero hia
  have h03 := (q t).distance 0 3 (by decide)
  have hia' := (q t).distance i a hia
  field_simp [hd, hz0, hw0]
  linear_combination hia' - h03

/-- Scale-order form of the arbitrary-rate skew branch.  These are direct
orders of positions, forces, and inverses of actual ZW solutions.  In
particular the 1--3 and 2--3 radii need not escape or have any fixed exponent. -/
structure SkewOrders (q : ℕ → ZWSystem ℂ 5 mass) where
  eps : ℕ → ℂ
  eps_zero : Tendsto eps atTop (𝓝 0)
  center : ℕ → ℂ
  z_small : ∀ i : Fin 5, i.val < 3 → (fun t => (q t).z i) =O[atTop] eps
  centered_w_small : ∀ i : Fin 5, i.val < 3 →
    (fun t => (q t).w i - center t) =O[atTop] eps
  cross_w_large : ∀ i a, Cross i a → eps =o[atTop] (fun t => (q t).w i - (q t).w a)
  attachment_w_subforce : (fun t => (q t).w 0 - (q t).w 3) =o[atTop]
    (fun t => (q t).wForce 0 3)
  other_attachment_bounded : (fun t => (q t).delta 1 4) =O[atTop] (fun _ => (1 : ℂ))
  opposite_z_small : ∀ i : Fin 5, i = 1 ∨ i = 2 →
    (fun t => (q t).z 0 - (q t).z 3) =o[atTop] (fun t => (q t).z i - (q t).z 3)
  same_w_comparable : ∀ i : Fin 5, i = 1 ∨ i = 2 →
    (fun t => (q t).w 0 - (q t).w 3) =O[atTop] (fun t => (q t).w i - (q t).w 3)
  far_inverse_zero : ∀ i a, (i = 0 ∧ a = 4) ∨ (i = 2 ∧ a = 4) ∨ (i = 3 ∧ a = 4) →
    Tendsto (fun t => (q t).delta i a) atTop (𝓝 0)

def SkewOrders.toRatios (h : SkewOrders q) : SkewRatios q where
  center := h.center
  z_zero i hi := (h.z_small i hi).trans_tendsto h.eps_zero
  centered_w_zero i hi := (h.centered_w_small i hi).trans_tendsto h.eps_zero
  cross_ratio_zero i a hia :=
    ((h.centered_w_small i hia.1).trans_isLittleO (h.cross_w_large i a hia)).tendsto_div_nhds_zero
  dominant_reciprocal_zero := inverse_zero_of_separation_small_force h.attachment_w_subforce
  inverse_ratios i a he := by
    have hd := inverse_zero_of_separation_small_force h.attachment_w_subforce
    have hdom : Tendsto (fun t => (q t).delta 0 3 / (q t).delta 0 3) atTop (𝓝 1) := by
      have hh : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1) := tendsto_const_nhds
      convert hh using 1
      funext t
      exact div_self ((q t).toNormalized.delta_ne_zero (by decide))
    have h14 : Tendsto (fun t => (q t).delta 1 4 / (q t).delta 0 3) atTop (𝓝 0) := by
      have hh := h.other_attachment_bounded.mul_isLittleO ((isLittleO_one_iff ℂ).2 hd)
      simp only [one_mul] at hh
      simpa only [div_eq_mul_inv, one_mul] using (isLittleO_one_iff ℂ).1 hh
    have h13 := relative_inverse_zero (q := q) (i := 1) (a := 3) (by decide)
      (h.opposite_z_small 1 (Or.inl rfl)) (h.same_w_comparable 1 (Or.inl rfl))
    have h23 := relative_inverse_zero (q := q) (i := 2) (a := 3) (by decide)
      (h.opposite_z_small 2 (Or.inr rfl)) (h.same_w_comparable 2 (Or.inr rfl))
    have far (i a : Fin 5) (hfar : (i = 0 ∧ a = 4) ∨ (i = 2 ∧ a = 4) ∨ (i = 3 ∧ a = 4)) :
        Tendsto (fun t => (q t).delta i a / (q t).delta 0 3) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using (h.far_inverse_zero i a hfar).mul hd
    fin_cases i <;> fin_cases a
    all_goals try norm_num [External, Cross, Fin.ext_iff] at he
    all_goals norm_num [Fin.ext_iff]
    · exact hdom
    · exact far 0 4 (by simp)
    · exact h13
    · exact h14
    · exact h23
    · exact far 2 4 (by simp)
    · exact far 3 4 (by simp)

theorem SkewOrders.false_of_constant_potential (h : SkewOrders q)
    (hm0 : mass 0 ≠ 0) (hm3 : mass 3 ≠ 0) (I0 : ℂ)
    (hI : ∀ t, (q t).toNormalized.unorderedPotential = I0) : False :=
  h.toRatios.false_of_constant_potential hm0 hm3 I0 hI

end CentralConfigurations.FiveBody.D9
