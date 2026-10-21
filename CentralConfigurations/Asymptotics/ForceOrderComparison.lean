import CentralConfigurations.Asymptotics.PairEstimates

/-!
# Force comparisons in the Section 4 order-comparing process

These are the algebraic rules (6)--(9). Squared and cubed identities keep the
actual inverse-distance branch. In the equal-order cases the conclusion is
two-sided comparability, as in Appendix II, rather than the strict inequality
printed in several of the prose rules. Both colors follow by `swap`.
-/

namespace CentralConfigurations

open Filter Asymptotics

namespace PairEstimateData

variable (p r : PairEstimateData)

theorem radius_ne_zero (t : ℕ) : p.radius t ≠ 0 := inv_ne_zero (p.delta_ne_zero t)

theorem zForce_sq_inverse (t : ℕ) :
    p.zForce t ^ 2 = (p.z t * p.w t ^ 3)⁻¹ := by
  apply mul_right_cancel₀ (mul_ne_zero (p.z_ne_zero t) (pow_ne_zero 3 (p.w_ne_zero t)))
  rw [inv_mul_cancel₀ (mul_ne_zero (p.z_ne_zero t) (pow_ne_zero 3 (p.w_ne_zero t)))]
  calc
    _ = (p.delta t ^ 2 * (p.z t * p.w t)) ^ 3 := by unfold zForce; ring
    _ = 1 := by rw [p.distance_eq]; norm_num

theorem zForce_radius_inverse (t : ℕ) :
    p.zForce t = p.z t * (p.radius t)⁻¹ ^ 3 := by
  simp only [zForce, radius, inv_inv, mul_comm]

theorem zForce_w_radius_inverse (t : ℕ) :
    p.zForce t = (p.w t * p.radius t)⁻¹ := by
  apply mul_right_cancel₀ (mul_ne_zero (p.w_ne_zero t) (p.radius_ne_zero t))
  rw [inv_mul_cancel₀ (mul_ne_zero (p.w_ne_zero t) (p.radius_ne_zero t))]
  rw [← mul_assoc, p.zForce_mul_w]
  exact mul_inv_cancel₀ (p.delta_ne_zero t)

theorem zForce_cube_opposite (t : ℕ) :
    p.zForce t ^ 3 = p.wForce t * (p.w t)⁻¹ ^ 4 := by
  apply mul_right_cancel₀ (pow_ne_zero 4 (p.w_ne_zero t))
  rw [mul_assoc, ← mul_pow, inv_mul_cancel₀ (p.w_ne_zero t), one_pow, mul_one]
  calc
    _ = p.wForce t * (p.delta t ^ 2 * (p.z t * p.w t)) ^ 3 := by
      unfold zForce wForce
      ring
    _ = p.wForce t := by rw [p.distance_eq]; ring

/-- Rule (6c), written in the direction of the smaller separations. -/
theorem zForce_littleO_of_separations
    (hz : p.z =O[atTop] r.z) (hw : p.w =O[atTop] r.w)
    (hstrict : p.z =o[atTop] r.z ∨ p.w =o[atTop] r.w) :
    r.zForce =o[atTop] p.zForce := by
  have hp : (fun t => p.z t * p.w t ^ 3) =o[atTop]
      (fun t => r.z t * r.w t ^ 3) := by
    rcases hstrict with h | h
    · exact h.mul_isBigO (hw.pow 3)
    · exact hz.mul_isLittleO (h.pow (by decide : 0 < 3))
  have hi := hp.inv_rev (Eventually.of_forall fun t he =>
    (mul_ne_zero (p.z_ne_zero t) (pow_ne_zero 3 (p.w_ne_zero t)) he).elim)
  have hs : (fun t => r.zForce t ^ 2) =o[atTop] (fun t => p.zForce t ^ 2) :=
    hi.congr (fun t => (r.zForce_sq_inverse t).symm) (fun t => (p.zForce_sq_inverse t).symm)
  exact hs.of_pow (by decide : (2 : ℕ) ≠ 0)

/-- The equal-order branch (6d), implemented as `{0}` in Appendix II. -/
theorem zForce_theta_of_separations
    (hz : p.z =Θ[atTop] r.z) (hw : p.w =Θ[atTop] r.w) :
    p.zForce =Θ[atTop] r.zForce := by
  apply theta_of_powers (by decide : (2 : ℕ) ≠ 0)
  exact theta_congr_pointwise (hz.mul (hw.pow 3)).inv
    (fun t => (p.zForce_sq_inverse t).symm) (fun t => (r.zForce_sq_inverse t).symm)

/-- Rule (6e). -/
theorem zForce_littleO_of_z_radius
    (hz : p.z =O[atTop] r.z) (hr : r.radius =O[atTop] p.radius)
    (hstrict : p.z =o[atTop] r.z ∨ r.radius =o[atTop] p.radius) :
    p.zForce =o[atTop] r.zForce := by
  have hi := hr.inv_rev (Eventually.of_forall fun t he => (r.radius_ne_zero t he).elim)
  have hp : (fun t => p.z t * (p.radius t)⁻¹ ^ 3) =o[atTop]
      (fun t => r.z t * (r.radius t)⁻¹ ^ 3) := by
    rcases hstrict with h | h
    · exact h.mul_isBigO (hi.pow 3)
    · have hl := h.inv_rev (Eventually.of_forall fun t he => (r.radius_ne_zero t he).elim)
      exact hz.mul_isLittleO (hl.pow (by decide : 0 < 3))
  exact hp.congr (fun t => (p.zForce_radius_inverse t).symm)
    (fun t => (r.zForce_radius_inverse t).symm)

/-- The equal-order branch (6f). -/
theorem zForce_theta_of_z_radius
    (hz : p.z =Θ[atTop] r.z) (hr : p.radius =Θ[atTop] r.radius) :
    p.zForce =Θ[atTop] r.zForce :=
  theta_congr_pointwise (hz.mul (hr.inv.pow 3))
    (fun t => (p.zForce_radius_inverse t).symm) (fun t => (r.zForce_radius_inverse t).symm)

/-- Rule (6g). -/
theorem zForce_littleO_of_w_radius
    (hw : p.w =O[atTop] r.w) (hr : p.radius =O[atTop] r.radius)
    (hstrict : p.w =o[atTop] r.w ∨ p.radius =o[atTop] r.radius) :
    r.zForce =o[atTop] p.zForce := by
  have hp : (fun t => p.w t * p.radius t) =o[atTop]
      (fun t => r.w t * r.radius t) := by
    rcases hstrict with h | h
    · exact h.mul_isBigO hr
    · exact hw.mul_isLittleO h
  have hi := hp.inv_rev (Eventually.of_forall fun t he =>
    (mul_ne_zero (p.w_ne_zero t) (p.radius_ne_zero t) he).elim)
  exact hi.congr (fun t => (r.zForce_w_radius_inverse t).symm)
    (fun t => (p.zForce_w_radius_inverse t).symm)

/-- The equal-order branch (6h). -/
theorem zForce_theta_of_w_radius
    (hw : p.w =Θ[atTop] r.w) (hr : p.radius =Θ[atTop] r.radius) :
    p.zForce =Θ[atTop] r.zForce :=
  theta_congr_pointwise (hw.mul hr).inv
    (fun t => (p.zForce_w_radius_inverse t).symm)
    (fun t => (r.zForce_w_radius_inverse t).symm)

/-- Rule (6i): a nonzero opposite-color stroke supplies the needed force bound. -/
theorem zForce_littleO_of_opposite_force
    (hf : p.wForce =O[atTop] r.wForce) (hw : r.w =o[atTop] p.w) :
    p.zForce =o[atTop] r.zForce := by
  have hi := hw.inv_rev (Eventually.of_forall fun t he => (r.w_ne_zero t he).elim)
  have hp := hf.mul_isLittleO (hi.pow (by decide : 0 < 4))
  have hs : (fun t => p.zForce t ^ 3) =o[atTop] (fun t => r.zForce t ^ 3) :=
    hp.congr (fun t => (p.zForce_cube_opposite t).symm)
      (fun t => (r.zForce_cube_opposite t).symm)
  exact hs.of_pow (by decide : (3 : ℕ) ≠ 0)

/-- Rule (6j). -/
theorem zForce_theta_of_opposite_force
    (hf : p.wForce =Θ[atTop] r.wForce) (hw : p.w =Θ[atTop] r.w) :
    p.zForce =Θ[atTop] r.zForce := by
  apply theta_of_powers (by decide : (3 : ℕ) ≠ 0)
  exact theta_congr_pointwise (hf.mul (hw.inv.pow 4))
    (fun t => (p.zForce_cube_opposite t).symm) (fun t => (r.zForce_cube_opposite t).symm)

/-- Rule (8c), for any position sequence `x`. -/
theorem position_littleO_zForce {x : ℕ → ℂ}
    (hx : x =O[atTop] p.z) (hr : p.radius =O[atTop] (fun _ => (1 : ℂ)))
    (hstrict : x =o[atTop] p.z ∨ p.radius =o[atTop] (fun _ => (1 : ℂ))) :
    x =o[atTop] p.zForce := by
  have hp : (fun t => x t * p.radius t ^ 3) =o[atTop] p.z := by
    rcases hstrict with h | h
    · simpa only [one_pow, mul_one] using h.mul_isBigO (hr.pow 3)
    · simpa only [one_pow, mul_one] using hx.mul_isLittleO (h.pow (by decide : 0 < 3))
  exact (hp.mul_isBigO (isBigO_refl (fun t => (p.radius t)⁻¹ ^ 3) atTop)).congr
    (fun t => by simp [p.radius_ne_zero t])
    (fun t => (p.zForce_radius_inverse t).symm)

/-- Rule (8d). -/
theorem zForce_theta_position {x : ℕ → ℂ}
    (hx : p.z =Θ[atTop] x) (hr : p.radius =Θ[atTop] (fun _ => (1 : ℂ))) :
    p.zForce =Θ[atTop] x :=
  theta_congr_pointwise (hx.mul (hr.inv.pow 3))
    (fun t => (p.zForce_radius_inverse t).symm) (fun _ => by simp)

theorem wForce_littleO_of_separations
    (hw : p.w =O[atTop] r.w) (hz : p.z =O[atTop] r.z)
    (hstrict : p.w =o[atTop] r.w ∨ p.z =o[atTop] r.z) :
    r.wForce =o[atTop] p.wForce :=
  p.swap.zForce_littleO_of_separations r.swap hw hz hstrict

theorem wForce_theta_of_separations
    (hw : p.w =Θ[atTop] r.w) (hz : p.z =Θ[atTop] r.z) :
    p.wForce =Θ[atTop] r.wForce :=
  p.swap.zForce_theta_of_separations r.swap hw hz

theorem wForce_littleO_of_w_radius
    (hw : p.w =O[atTop] r.w) (hr : r.radius =O[atTop] p.radius)
    (hstrict : p.w =o[atTop] r.w ∨ r.radius =o[atTop] p.radius) :
    p.wForce =o[atTop] r.wForce :=
  p.swap.zForce_littleO_of_z_radius r.swap hw hr hstrict

theorem wForce_theta_of_w_radius
    (hw : p.w =Θ[atTop] r.w) (hr : p.radius =Θ[atTop] r.radius) :
    p.wForce =Θ[atTop] r.wForce :=
  p.swap.zForce_theta_of_z_radius r.swap hw hr

theorem wForce_littleO_of_z_radius
    (hz : p.z =O[atTop] r.z) (hr : p.radius =O[atTop] r.radius)
    (hstrict : p.z =o[atTop] r.z ∨ p.radius =o[atTop] r.radius) :
    r.wForce =o[atTop] p.wForce :=
  p.swap.zForce_littleO_of_w_radius r.swap hz hr hstrict

theorem wForce_theta_of_z_radius
    (hz : p.z =Θ[atTop] r.z) (hr : p.radius =Θ[atTop] r.radius) :
    p.wForce =Θ[atTop] r.wForce :=
  p.swap.zForce_theta_of_w_radius r.swap hz hr

theorem wForce_littleO_of_opposite_force
    (hf : p.zForce =O[atTop] r.zForce) (hz : r.z =o[atTop] p.z) :
    p.wForce =o[atTop] r.wForce :=
  p.swap.zForce_littleO_of_opposite_force r.swap hf hz

theorem wForce_theta_of_opposite_force
    (hf : p.zForce =Θ[atTop] r.zForce) (hz : p.z =Θ[atTop] r.z) :
    p.wForce =Θ[atTop] r.wForce :=
  p.swap.zForce_theta_of_opposite_force r.swap hf hz

theorem position_littleO_wForce {x : ℕ → ℂ}
    (hx : x =O[atTop] p.w) (hr : p.radius =O[atTop] (fun _ => (1 : ℂ)))
    (hstrict : x =o[atTop] p.w ∨ p.radius =o[atTop] (fun _ => (1 : ℂ))) :
    x =o[atTop] p.wForce := p.swap.position_littleO_zForce hx hr hstrict

theorem wForce_theta_position {x : ℕ → ℂ}
    (hx : p.w =Θ[atTop] x) (hr : p.radius =Θ[atTop] (fun _ => (1 : ℂ))) :
    p.wForce =Θ[atTop] x := p.swap.zForce_theta_position hx hr

end PairEstimateData
end CentralConfigurations
