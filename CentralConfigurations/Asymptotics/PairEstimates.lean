import CentralConfigurations.Asymptotics.GaugeBounds
import CentralConfigurations.Asymptotics.OrderSemantics

/-!
# Pair estimates from the normalized equations

Chang (2023), Theorems 2.3--2.4. The small parameter is epsilon and the
common vector scale is epsilon^(-2). The abstract input below consists only
of the distance equation and the four immediate upper bounds. It is
constructed from every balanced sequence of actual solutions below.
All inverse distances retain their complex branch; no principal root of a
complex separation is chosen.
-/

namespace CentralConfigurations

noncomputable section

open Filter Asymptotics
open scoped Topology

theorem theta_of_powers {f g : ℕ → ℂ} {k : ℕ} (hk : k ≠ 0)
    (h : (fun t => f t ^ k) =Θ[atTop] (fun t => g t ^ k)) : f =Θ[atTop] g :=
  ⟨IsBigO.of_pow hk h.1, IsBigO.of_pow hk h.2⟩

theorem theta_congr_pointwise {f g f' g' : ℕ → ℂ} (h : f =Θ[atTop] g)
    (hf : ∀ t, f t = f' t) (hg : ∀ t, g t = g' t) : f' =Θ[atTop] g' :=
  ⟨h.1.congr hf hg, h.2.congr hg hf⟩

/-- Saturation of a product of two individually bounded nonzero factors forces
both factors to attain their own bounds. -/
theorem theta_product_factors {f₁ f₂ g₁ g₂ : ℕ → ℂ}
    (hf₁ : ∀ t, f₁ t ≠ 0) (hf₂ : ∀ t, f₂ t ≠ 0)
    (hg₁ : ∀ t, g₁ t ≠ 0) (hg₂ : ∀ t, g₂ t ≠ 0)
    (h₁ : f₁ =O[atTop] g₁) (h₂ : f₂ =O[atTop] g₂)
    (h : (fun t => f₁ t * f₂ t) =Θ[atTop] (fun t => g₁ t * g₂ t)) :
    f₁ =Θ[atTop] g₁ ∧ f₂ =Θ[atTop] g₂ := by
  refine ⟨⟨h₁, ?_⟩, ⟨h₂, ?_⟩⟩
  · exact (h.2.mul (h₂.inv_rev (Eventually.of_forall fun t ht => (hf₂ t ht).elim))).congr
      (fun t => by simp [hg₂ t]) (fun t => by simp [hf₂ t])
  · exact (h.2.mul (h₁.inv_rev (Eventually.of_forall fun t ht => (hf₁ t ht).elim))).congr
      (fun t => by rw [mul_comm (g₁ t)]; simp [hg₁ t])
      (fun t => by rw [mul_comm (f₁ t)]; simp [hf₁ t])

structure PairEstimateData where
  z : ℕ → ℂ
  w : ℕ → ℂ
  delta : ℕ → ℂ
  eps : ℕ → ℂ
  eps_ne_zero : ∀ t, eps t ≠ 0
  distance_eq : ∀ t, delta t ^ 2 * (z t * w t) = 1
  z_upper : z =O[atTop] (fun t => (eps t)⁻¹ ^ 2)
  w_upper : w =O[atTop] (fun t => (eps t)⁻¹ ^ 2)
  zForce_upper : (fun t => delta t ^ 3 * z t) =O[atTop] (fun t => (eps t)⁻¹ ^ 2)
  wForce_upper : (fun t => delta t ^ 3 * w t) =O[atTop] (fun t => (eps t)⁻¹ ^ 2)

namespace PairEstimateData

variable (p : PairEstimateData)

def scale : ℕ → ℂ := fun t => (p.eps t)⁻¹ ^ 2
def radius : ℕ → ℂ := fun t => (p.delta t)⁻¹
def zForce : ℕ → ℂ := fun t => p.delta t ^ 3 * p.z t
def wForce : ℕ → ℂ := fun t => p.delta t ^ 3 * p.w t

theorem delta_ne_zero (t : ℕ) : p.delta t ≠ 0 := by
  intro h
  have hd := p.distance_eq t
  simp [h] at hd

theorem z_ne_zero (t : ℕ) : p.z t ≠ 0 := by
  intro h
  have hd := p.distance_eq t
  simp [h] at hd

theorem w_ne_zero (t : ℕ) : p.w t ≠ 0 := by
  intro h
  have hd := p.distance_eq t
  simp [h] at hd

theorem scale_ne_zero (t : ℕ) : p.scale t ≠ 0 :=
  pow_ne_zero _ (inv_ne_zero (p.eps_ne_zero t))

theorem zForce_ne_zero (t : ℕ) : p.zForce t ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (p.delta_ne_zero t)) (p.z_ne_zero t)

theorem wForce_ne_zero (t : ℕ) : p.wForce t ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (p.delta_ne_zero t)) (p.w_ne_zero t)

theorem force_product (t : ℕ) : p.zForce t * p.wForce t = p.delta t ^ 4 := by
  calc
    _ = p.delta t ^ 4 * (p.delta t ^ 2 * (p.z t * p.w t)) := by
      unfold zForce wForce
      ring
    _ = _ := by rw [p.distance_eq]; ring

theorem wForce_mul_z (t : ℕ) : p.wForce t * p.z t = p.delta t := by
  calc
    _ = p.delta t * (p.delta t ^ 2 * (p.z t * p.w t)) := by
      unfold wForce
      ring
    _ = _ := by rw [p.distance_eq]; ring

theorem zForce_mul_w (t : ℕ) : p.zForce t * p.w t = p.delta t := by
  calc
    _ = p.delta t * (p.delta t ^ 2 * (p.z t * p.w t)) := by
      unfold zForce
      ring
    _ = _ := by rw [p.distance_eq]; ring

theorem radius_sq (t : ℕ) : p.radius t ^ 2 = p.z t * p.w t := by
  apply (mul_left_cancel₀ (pow_ne_zero 2 (p.delta_ne_zero t)))
  rw [p.distance_eq]
  simp [radius, p.delta_ne_zero]

theorem inv_z_cube (t : ℕ) : (p.z t)⁻¹ ^ 3 = p.wForce t ^ 2 * p.w t := by
  apply (mul_right_cancel₀ (pow_ne_zero 3 (p.z_ne_zero t)))
  calc
    _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ (p.z_ne_zero t), one_pow]
    _ = (p.delta t ^ 2 * (p.z t * p.w t)) ^ 3 := by rw [p.distance_eq]; ring
    _ = _ := by unfold wForce; ring

def swap : PairEstimateData where
  z := p.w
  w := p.z
  delta := p.delta
  eps := p.eps
  eps_ne_zero := p.eps_ne_zero
  distance_eq t := by rw [mul_comm (p.w t)]; exact p.distance_eq t
  z_upper := p.w_upper
  w_upper := p.z_upper
  zForce_upper := p.wForce_upper
  wForce_upper := p.zForce_upper

/-- The inverse distance is O(epsilon^(-1)). -/
theorem delta_upper : p.delta =O[atTop] (fun t => (p.eps t)⁻¹) := by
  apply IsBigO.of_pow (n := 4) (by decide)
  exact (p.zForce_upper.mul p.wForce_upper).congr
    (fun t => p.force_product t) (fun t => by dsimp; ring)

/-- Theorem 2.3(1), lower bound: epsilon = O(r). -/
theorem radius_lower : p.eps =O[atTop] p.radius := by
  simpa only [inv_inv] using p.delta_upper.inv_rev
    (Eventually.of_forall fun t h => (p.delta_ne_zero t h).elim)

/-- Theorem 2.3(1), upper bound: r = O(epsilon^(-2)). -/
theorem radius_upper : p.radius =O[atTop] p.scale := by
  apply IsBigO.of_pow (n := 2) (by decide)
  exact (p.z_upper.mul p.w_upper).congr
    (fun t => (p.radius_sq t).symm) (fun t => by dsimp [scale]; ring)

theorem inv_z_upper : (fun t => (p.z t)⁻¹) =O[atTop] p.scale := by
  apply IsBigO.of_pow (n := 3) (by decide)
  exact ((p.wForce_upper.pow 2).mul p.w_upper).congr
    (fun t => (p.inv_z_cube t).symm) (fun t => by dsimp [scale]; ring)

/-- Theorem 2.3(2), lower separation bound. -/
theorem z_lower : (fun t => p.eps t ^ 2) =O[atTop] p.z := by
  simpa only [scale, inv_pow, inv_inv] using p.inv_z_upper.inv_rev
    (Eventually.of_forall fun t h => (inv_ne_zero (p.z_ne_zero t) h).elim)

theorem w_lower : (fun t => p.eps t ^ 2) =O[atTop] p.w := p.swap.z_lower

/-- Theorem 2.3(3), the double-edge distance criterion. -/
theorem double_force_iff_radius :
    (p.zForce =Θ[atTop] p.scale ∧ p.wForce =Θ[atTop] p.scale) ↔
      p.radius =Θ[atTop] p.eps := by
  constructor
  · rintro ⟨hz, hw⟩
    have hpow : (fun t => p.delta t ^ 4) =Θ[atTop] (fun t => (p.eps t)⁻¹ ^ 4) :=
      theta_congr_pointwise (hz.mul hw)
      (fun t => p.force_product t) (fun t => by dsimp [scale]; ring)
    have hd : p.delta =Θ[atTop] (fun t => (p.eps t)⁻¹) :=
      theta_of_powers (k := 4) (by decide) hpow
    simpa only [inv_inv] using hd.inv
  · intro hr
    have hd : p.delta =Θ[atTop] (fun t => (p.eps t)⁻¹) := by
      simpa only [radius, inv_inv] using hr.inv
    have hprod : (fun t => p.zForce t * p.wForce t) =Θ[atTop]
        (fun t => p.scale t * p.scale t) := theta_congr_pointwise (hd.pow 4)
      (fun t => (p.force_product t).symm) (fun t => by dsimp [scale]; ring)
    exact theta_product_factors p.zForce_ne_zero p.wForce_ne_zero
      p.scale_ne_zero p.scale_ne_zero p.zForce_upper p.wForce_upper hprod

/-- A z-stroke forces a uniform upper order bound on the distance. -/
theorem stroke_radius_upper (hz : p.zForce =Θ[atTop] p.scale) :
    p.radius =O[atTop] (fun _ => (1 : ℂ)) := by
  have hpow : (fun _ => (1 : ℂ)) =O[atTop] (fun t => p.delta t ^ 3) := by
    exact (hz.2.mul (p.z_upper.inv_rev
      (Eventually.of_forall fun t h => (p.z_ne_zero t h).elim))).congr
      (fun t => mul_inv_cancel₀ (p.scale_ne_zero t))
      (fun t => by simp [zForce, p.z_ne_zero t])
  have hd : (fun _ => (1 : ℂ)) =O[atTop] p.delta := by
    apply IsBigO.of_pow (n := 3) (by decide)
    change (fun _ => (1 : ℂ) ^ 3) =O[atTop] (fun t => p.delta t ^ 3)
    simpa only [one_pow] using hpow
  simpa only [inv_one] using hd.inv_rev (Eventually.of_forall fun _ h => (one_ne_zero h).elim)

/-- A z-stroke improves the upper bound of the opposite-color separation. -/
theorem stroke_w_upper (hz : p.zForce =Θ[atTop] p.scale) : p.w =O[atTop] p.eps := by
  have hw (t : ℕ) : p.delta t * (p.zForce t)⁻¹ = p.w t := by
    rw [← p.zForce_mul_w t, mul_comm (p.zForce t), mul_assoc,
      mul_inv_cancel₀ (p.zForce_ne_zero t), mul_one]
  exact (p.delta_upper.mul hz.inv.1).congr hw (fun t => by
    dsimp [scale]
    field_simp [p.eps_ne_zero t])

/-- A z-stroke improves the lower bound of its own separation. -/
theorem stroke_z_lower (hz : p.zForce =Θ[atTop] p.scale) : p.eps =O[atTop] p.z := by
  have hpow : (fun t => p.eps t ^ 2) =O[atTop] (fun t => p.z t * p.eps t) :=
    ((p.radius_lower.pow 2).congr_right (fun t => p.radius_sq t)).trans
      ((isBigO_refl p.z atTop).mul (p.stroke_w_upper hz))
  exact (hpow.mul (isBigO_refl (fun t => (p.eps t)⁻¹) atTop)).congr
    (fun t => by field_simp [p.eps_ne_zero t])
    (fun t => by simp [p.eps_ne_zero t])

/-- Theorem 2.3(4), stated with a maximal z-stroke. Exclusion of an additional
w-stroke follows separately when epsilon tends to zero. -/
theorem maximal_iff_w_small :
    (p.zForce =Θ[atTop] p.scale ∧ p.z =Θ[atTop] p.scale) ↔
      p.w =Θ[atTop] (fun t => p.eps t ^ 2) := by
  constructor
  · rintro ⟨hz, hs⟩
    have hpow : (fun t => (p.w t)⁻¹ ^ 3) =Θ[atTop] (fun t => p.scale t ^ 3) :=
      theta_congr_pointwise ((hz.pow 2).mul hs)
        (fun t => (p.swap.inv_z_cube t).symm) (fun t => by ring)
    have h : (fun t => (p.w t)⁻¹) =Θ[atTop] p.scale :=
      theta_of_powers (by decide : (3 : ℕ) ≠ 0) hpow
    simpa only [scale, inv_pow, inv_inv] using h.inv
  · intro hw
    have hi : (fun t => (p.w t)⁻¹) =Θ[atTop] p.scale := by
      exact theta_congr_pointwise hw.inv (fun _ => rfl) (fun t => by
        dsimp [scale]
        rw [inv_pow])
    have hprod : (fun t => p.zForce t ^ 2 * p.z t) =Θ[atTop]
        (fun t => p.scale t ^ 2 * p.scale t) :=
      theta_congr_pointwise (hi.pow 3)
        (fun t => p.swap.inv_z_cube t) (fun t => by ring)
    have hf := theta_product_factors
      (fun t => pow_ne_zero 2 (p.zForce_ne_zero t)) p.z_ne_zero
      (fun t => pow_ne_zero 2 (p.scale_ne_zero t)) p.scale_ne_zero
      (p.zForce_upper.pow 2) p.z_upper hprod
    exact ⟨theta_of_powers (by decide : (2 : ℕ) ≠ 0) hf.1, hf.2⟩

/-- Theorem 2.4(4): under a z-stroke, the small-distance boundary is exactly
the epsilon order for the z-separation. -/
theorem stroke_radius_iff_z_epsilon (hz : p.zForce =Θ[atTop] p.scale) :
    p.radius =Θ[atTop] p.eps ↔ p.z =Θ[atTop] p.eps := by
  constructor
  · intro hr
    have hw := (p.double_force_iff_radius.mpr hr).2
    have hd : p.delta =Θ[atTop] (fun t => (p.eps t)⁻¹) := by
      simpa only [radius, inv_inv] using hr.inv
    exact theta_congr_pointwise (hd.mul hw.inv)
      (fun t => by rw [← p.wForce_mul_z t, mul_comm (p.wForce t), mul_assoc,
        mul_inv_cancel₀ (p.wForce_ne_zero t), mul_one])
      (fun t => by dsimp [scale]; field_simp [p.eps_ne_zero t])
  · intro hs
    have hpow : (fun t => p.delta t ^ 3) =Θ[atTop] (fun t => (p.eps t)⁻¹ ^ 3) :=
      theta_congr_pointwise (hz.mul hs.inv)
        (fun t => by simp [zForce, p.z_ne_zero t]) (fun t => by dsimp [scale]; ring)
    have hd := theta_of_powers (by decide : (3 : ℕ) ≠ 0) hpow
    simpa only [inv_inv] using hd.inv

/-- Theorem 2.4(4), the equivalent opposite-color separation criterion. -/
theorem stroke_radius_iff_w_epsilon (hz : p.zForce =Θ[atTop] p.scale) :
    p.radius =Θ[atTop] p.eps ↔ p.w =Θ[atTop] p.eps := by
  constructor
  · intro hr
    have hw := (p.double_force_iff_radius.mpr hr).2
    exact (p.swap.stroke_radius_iff_z_epsilon hw).mp hr
  · intro hw
    have hd : p.delta =Θ[atTop] (fun t => (p.eps t)⁻¹) :=
      theta_congr_pointwise (hz.mul hw)
        (fun t => p.zForce_mul_w t) (fun t => by dsimp [scale]; field_simp [p.eps_ne_zero t])
    simpa only [inv_inv] using hd.inv

/-- Theorem 2.4(5): a z-stroke is maximal exactly at the unit-distance boundary. -/
theorem stroke_radius_iff_z_maximal (hz : p.zForce =Θ[atTop] p.scale) :
    p.radius =Θ[atTop] (fun _ => (1 : ℂ)) ↔ p.z =Θ[atTop] p.scale := by
  constructor
  · intro hr
    exact theta_congr_pointwise (hz.mul (hr.pow 3))
      (fun t => by simp [zForce, radius, mul_right_comm _ (p.z t), p.delta_ne_zero t])
      (fun _ => by ring)
  · intro hs
    have hpow : (fun t => p.delta t ^ 3) =Θ[atTop] (fun _ => (1 : ℂ) ^ 3) :=
      theta_congr_pointwise (hz.mul hs.inv)
        (fun t => by simp [zForce, p.z_ne_zero t])
        (fun t => by simp [p.scale_ne_zero t])
    have hd := theta_of_powers (by decide : (3 : ℕ) ≠ 0) hpow
    simpa only [inv_one] using hd.inv

/-- The remaining equivalence in Theorem 2.4(5). -/
theorem stroke_maximal_iff_w_small (hz : p.zForce =Θ[atTop] p.scale) :
    p.z =Θ[atTop] p.scale ↔ p.w =Θ[atTop] (fun t => p.eps t ^ 2) := by
  exact ⟨fun hs => p.maximal_iff_w_small.mp ⟨hz, hs⟩,
    fun hw => (p.maximal_iff_w_small.mpr hw).2⟩

/-- Useful for the triangle rule: upper bounds of epsilon for both separations
already force a double edge; no lower separation hypothesis is added. -/
theorem small_separations_iff_double :
    (p.z =O[atTop] p.eps ∧ p.w =O[atTop] p.eps) ↔
      (p.zForce =Θ[atTop] p.scale ∧ p.wForce =Θ[atTop] p.scale) := by
  constructor
  · rintro ⟨hz, hw⟩
    have hr : p.radius =O[atTop] p.eps := by
      apply IsBigO.of_pow (n := 2) (by decide)
      exact (hz.mul hw).congr (fun t => (p.radius_sq t).symm) (fun t => by dsimp; ring)
    exact p.double_force_iff_radius.mpr ⟨hr, p.radius_lower⟩
  · intro hf
    have hr := p.double_force_iff_radius.mp hf
    exact ⟨((p.stroke_radius_iff_z_epsilon hf.1).mp hr).1,
      ((p.stroke_radius_iff_w_epsilon hf.1).mp hr).1⟩

/-- For an exclusively z-colored edge, the own-color separation is strictly
larger than epsilon and the opposite-color separation is strictly smaller.
The zero leading coefficient of the absent stroke supplies the little-o input. -/
theorem single_z_separations (hz : p.zForce =Θ[atTop] p.scale)
    (hw : p.wForce =o[atTop] p.scale) :
    p.eps =o[atTop] p.z ∧ p.w =o[atTop] p.eps := by
  have hpow : (fun t => p.delta t ^ 4) =o[atTop] (fun t => (p.eps t)⁻¹ ^ 4) :=
    (hz.1.mul_isLittleO hw).congr (fun t => p.force_product t)
      (fun t => by dsimp [scale]; ring)
  have hd : p.delta =o[atTop] (fun t => (p.eps t)⁻¹) :=
    hpow.of_pow (by decide : (4 : ℕ) ≠ 0)
  have hi : (fun t => (p.z t)⁻¹) =o[atTop] (fun t => (p.eps t)⁻¹) :=
    ((hd.pow (by decide : 0 < (3 : ℕ))).mul_isBigO hz.inv.1).congr
      (fun t => by dsimp [zForce]; field_simp [p.delta_ne_zero t, p.z_ne_zero t])
      (fun t => by dsimp [scale]; field_simp [p.eps_ne_zero t])
  refine ⟨?_, ?_⟩
  · simpa only [inv_inv] using hi.inv_rev
      (Eventually.of_forall fun t h => (inv_ne_zero (p.z_ne_zero t) h).elim)
  · exact (hd.mul_isBigO hz.inv.1).congr
      (fun t => by rw [← p.zForce_mul_w t, mul_comm (p.zForce t), mul_assoc,
        mul_inv_cancel₀ (p.zForce_ne_zero t), mul_one])
      (fun t => by dsimp [scale]; field_simp [p.eps_ne_zero t])

/-- The complete order assertions of Estimate 1. The term "maximal" here
means a stroke whose own separation attains the common scale. -/
structure EstimateOne : Prop where
  distance_lower : p.eps =O[atTop] p.radius
  distance_upper : p.radius =O[atTop] p.scale
  z_lower : (fun t => p.eps t ^ 2) =O[atTop] p.z
  z_upper : p.z =O[atTop] p.scale
  w_lower : (fun t => p.eps t ^ 2) =O[atTop] p.w
  w_upper : p.w =O[atTop] p.scale
  double_iff : (p.zForce =Θ[atTop] p.scale ∧ p.wForce =Θ[atTop] p.scale) ↔
    p.radius =Θ[atTop] p.eps
  maximal_iff : (p.zForce =Θ[atTop] p.scale ∧ p.z =Θ[atTop] p.scale) ↔
    p.w =Θ[atTop] (fun t => p.eps t ^ 2)

theorem estimate_one : p.EstimateOne :=
  ⟨p.radius_lower, p.radius_upper, p.z_lower, p.z_upper, p.w_lower, p.w_upper,
    p.double_force_iff_radius, p.maximal_iff_w_small⟩

/-- The complete order assertions of Estimate 2 under a z-stroke. -/
structure EstimateTwo : Prop where
  distance_lower : p.eps =O[atTop] p.radius
  distance_upper : p.radius =O[atTop] (fun _ => (1 : ℂ))
  z_lower : p.eps =O[atTop] p.z
  z_upper : p.z =O[atTop] p.scale
  w_lower : (fun t => p.eps t ^ 2) =O[atTop] p.w
  w_upper : p.w =O[atTop] p.eps
  double_iff : p.wForce =Θ[atTop] p.scale ↔ p.radius =Θ[atTop] p.eps
  small_z_iff : p.radius =Θ[atTop] p.eps ↔ p.z =Θ[atTop] p.eps
  small_w_iff : p.radius =Θ[atTop] p.eps ↔ p.w =Θ[atTop] p.eps
  maximal_distance_iff : p.radius =Θ[atTop] (fun _ => (1 : ℂ)) ↔ p.z =Θ[atTop] p.scale
  maximal_w_iff : p.z =Θ[atTop] p.scale ↔ p.w =Θ[atTop] (fun t => p.eps t ^ 2)

theorem estimate_two (hz : p.zForce =Θ[atTop] p.scale) : p.EstimateTwo :=
  ⟨p.radius_lower, p.stroke_radius_upper hz, p.stroke_z_lower hz, p.z_upper,
    p.w_lower, p.stroke_w_upper hz,
    ⟨fun hw => p.double_force_iff_radius.mp ⟨hz, hw⟩,
      fun hr => (p.double_force_iff_radius.mpr hr).2⟩,
    p.stroke_radius_iff_z_epsilon hz, p.stroke_radius_iff_w_epsilon hz,
    p.stroke_radius_iff_z_maximal hz, p.stroke_maximal_iff_w_small hz⟩

end PairEstimateData

namespace ZWSystem

variable {n : ℕ} {mass : Fin n → ℂ}

noncomputable def epsilon (q : ZWSystem ℂ n mass) : ℝ := (Real.sqrt ‖q.zVector‖)⁻¹

theorem epsilon_pos (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) :
    0 < q.epsilon :=
  inv_pos.mpr (Real.sqrt_pos.mpr (norm_pos_iff.mpr (q.zVector_ne_zero i j hij)))

theorem epsilon_scale (q : ZWSystem ℂ n mass) :
    ((q.epsilon : ℂ)⁻¹) ^ 2 = (‖q.zVector‖ : ℂ) := by
  simp only [epsilon, Complex.ofReal_inv, inv_inv, ← Complex.ofReal_pow,
    Real.sq_sqrt (norm_nonneg _)]

theorem epsilon_tendsto_zero (q : ℕ → ZWSystem ℂ n mass)
    (h : Tendsto (fun t => ‖(q t).zVector‖) atTop atTop) :
    Tendsto (fun t => (q t).epsilon) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp h)

/-- The estimate input is produced by genuine balanced solutions, not assumed
as a property of candidate diagrams. -/
noncomputable def pairEstimateData (q : ℕ → ZWSystem ℂ n mass)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j : Fin n) (hij : i ≠ j) : PairEstimateData where
  z t := (q t).z i - (q t).z j
  w t := (q t).w i - (q t).w j
  delta t := (q t).delta i j
  eps t := ((q t).epsilon : ℂ)
  eps_ne_zero t := Complex.ofReal_ne_zero.mpr (ne_of_gt ((q t).epsilon_pos i j hij))
  distance_eq t := (q t).distance i j hij
  z_upper := IsBigO.of_bound 2 (Eventually.of_forall fun t => by
    rw [(q t).epsilon_scale, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _)]
    exact (q t).norm_z_separation_le i j)
  w_upper := IsBigO.of_bound 2 (Eventually.of_forall fun t => by
    rw [(q t).epsilon_scale, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), hb t]
    exact (q t).swap.norm_z_separation_le i j)
  zForce_upper := IsBigO.of_bound 1 (Eventually.of_forall fun t => by
    rw [(q t).epsilon_scale, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), one_mul]
    exact (q t).norm_zForce_le i j)
  wForce_upper := IsBigO.of_bound 1 (Eventually.of_forall fun t => by
    rw [(q t).epsilon_scale, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (norm_nonneg _), one_mul, hb t]
    exact (q t).swap.norm_zForce_le i j)

end ZWSystem

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)

/-- Exchange colors while retaining the canonical inverse-norm scale.
Balance is exactly what justifies this change of scale expression. -/
def swapBalanced : ScaledZWLimit (fun t => (q t).swap)
    (fun t => ((q t).swap).inverseScale) where
  z := l.w
  w := l.z
  z_position i := by
    change Tendsto (fun t => (‖(q t).wVector‖ : ℂ)⁻¹ * (q t).w i) atTop _
    simpa only [← hb, ZWSystem.inverseScale] using l.w_position i
  w_position i := by
    change Tendsto (fun t => (‖(q t).wVector‖ : ℂ)⁻¹ * (q t).z i) atTop _
    simpa only [← hb, ZWSystem.inverseScale] using l.z_position i
  z_force i j := by
    change Tendsto (fun t => (‖(q t).wVector‖ : ℂ)⁻¹ * (q t).wForce i j) atTop _
    simpa only [← hb, ZWSystem.inverseScale] using l.w_force i j
  w_force i j := by
    change Tendsto (fun t => (‖(q t).wVector‖ : ℂ)⁻¹ * (q t).zForce i j) atTop _
    simpa only [← hb, ZWSystem.inverseScale] using l.z_force i j

variable (i j : Fin n) (hij : i ≠ j)
include hb hij

theorem pair_z_stroke_iff :
    (ZWSystem.pairEstimateData q hb i j hij).zForce =Θ[atTop]
      (ZWSystem.pairEstimateData q hb i j hij).scale ↔ l.z.force i j ≠ 0 := by
  change ((fun t => (q t).zForce i j) =Θ[atTop]
    (fun t => (((q t).epsilon : ℂ)⁻¹) ^ 2)) ↔ _
  simp only [ZWSystem.epsilon_scale]
  exact l.z_stroke_order_iff i j hij i j

theorem pair_w_stroke_iff :
    (ZWSystem.pairEstimateData q hb i j hij).wForce =Θ[atTop]
      (ZWSystem.pairEstimateData q hb i j hij).scale ↔ l.w.force i j ≠ 0 := by
  change ((fun t => (q t).wForce i j) =Θ[atTop]
    (fun t => (((q t).epsilon : ℂ)⁻¹) ^ 2)) ↔ _
  simp only [ZWSystem.epsilon_scale]
  exact l.w_stroke_order_iff i j hij i j

theorem pair_z_absent_iff :
    (ZWSystem.pairEstimateData q hb i j hij).zForce =o[atTop]
      (ZWSystem.pairEstimateData q hb i j hij).scale ↔ l.z.force i j = 0 := by
  change ((fun t => (q t).zForce i j) =o[atTop]
    (fun t => (((q t).epsilon : ℂ)⁻¹) ^ 2)) ↔ _
  simp only [ZWSystem.epsilon_scale]
  exact normalized_littleO_iff (fun t => Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i j hij))) (l.z_force i j)

theorem pair_w_absent_iff :
    (ZWSystem.pairEstimateData q hb i j hij).wForce =o[atTop]
      (ZWSystem.pairEstimateData q hb i j hij).scale ↔ l.w.force i j = 0 := by
  change ((fun t => (q t).wForce i j) =o[atTop]
    (fun t => (((q t).epsilon : ℂ)⁻¹) ^ 2)) ↔ _
  simp only [ZWSystem.epsilon_scale]
  exact normalized_littleO_iff (fun t => Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i j hij))) (l.w_force i j)

theorem pair_z_maximal_iff :
    (ZWSystem.pairEstimateData q hb i j hij).z =Θ[atTop]
      (ZWSystem.pairEstimateData q hb i j hij).scale ↔ l.z.position i ≠ l.z.position j := by
  change ((fun t => (q t).z i - (q t).z j) =Θ[atTop]
    (fun t => (((q t).epsilon : ℂ)⁻¹) ^ 2)) ↔ _
  simp only [ZWSystem.epsilon_scale]
  exact l.z_separation_order_iff i j hij i j

/-- Estimate 2 for a stroke of an actual normalized limit. -/
theorem z_stroke_estimate_two (hz : l.z.force i j ≠ 0) :
    (ZWSystem.pairEstimateData q hb i j hij).EstimateTwo :=
  PairEstimateData.estimate_two _ ((l.pair_z_stroke_iff hb i j hij).mpr hz)

theorem w_stroke_estimate_two (hw : l.w.force i j ≠ 0) :
    (ZWSystem.pairEstimateData q hb i j hij).swap.EstimateTwo :=
  PairEstimateData.estimate_two _ ((l.pair_w_stroke_iff hb i j hij).mpr hw)

/-- Theorem 2.3(4) in the source's exclusive edge convention. A maximal
z-stroke cannot also be a w-stroke when the common scale diverges. -/
theorem maximal_z_edge_iff_w_small
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    (l.z.force i j ≠ 0 ∧ l.w.force i j = 0 ∧ l.z.position i ≠ l.z.position j) ↔
      (fun t => (q t).w i - (q t).w j) =Θ[atTop]
        (fun t => ((q t).epsilon : ℂ) ^ 2) := by
  let p := ZWSystem.pairEstimateData q hb i j hij
  constructor
  · rintro ⟨hz, _, hm⟩
    exact p.maximal_iff_w_small.mp
      ⟨(l.pair_z_stroke_iff hb i j hij).mpr hz, (l.pair_z_maximal_iff hb i j hij).mpr hm⟩
  · intro hw
    have hf := p.maximal_iff_w_small.mpr hw
    have hz := (l.pair_z_stroke_iff hb i j hij).mp hf.1
    have hm := (l.pair_z_maximal_iff hb i j hij).mp hf.2
    refine ⟨hz, ?_, hm⟩
    by_contra hn
    exact hm (l.w_stroke_z_close ha i j hij hn)

end ScaledZWLimit
end
end CentralConfigurations
