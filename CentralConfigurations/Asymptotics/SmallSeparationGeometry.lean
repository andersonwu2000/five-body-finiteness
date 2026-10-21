import CentralConfigurations.Asymptotics.IsolatedLeadingPositions

/-!
# Small separation geometry from the exact pair identity

Leading w-position coincidence makes the normalization scale strictly
smaller than the actual z-separation. A maximal w-pair gives the converse
boundedness. Both statements retain complex phases and use no chosen root.
-/

namespace CentralConfigurations

open Filter Asymptotics
open scoped Topology

namespace ZWSystem

theorem wForce_sq_zsep_cube_wsep {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) :
    q.wForce i j ^ 2 * (q.z i - q.z j) ^ 3 * (q.w i - q.w j) = 1 := by
  calc
    _ = (q.delta i j ^ 2 * ((q.z i - q.z j) * (q.w i - q.w j))) ^ 3 := by
      dsimp [ZWSystem.wForce]
      ring
    _ = 1 := by rw [q.distance i j hij]; ring

end ZWSystem

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
  {a : ℕ → ℂ} (l : ScaledZWLimit q a)

theorem scale_littleO_z_separation_of_equal_w_positions
    (i j : Fin n) (hij : i ≠ j) (hp : l.w.position i = l.w.position j) :
    a =o[atTop] (fun t => (q t).z i - (q t).z j) := by
  have hw : Tendsto (fun t => a t * ((q t).w i - (q t).w j)) atTop (𝓝 0) := by
    simpa only [mul_sub, hp, sub_self] using (l.w_position i).sub (l.w_position j)
  have hc : Tendsto (fun t => (a t / ((q t).z i - (q t).z j)) ^ 3) atTop (𝓝 0) := by
    convert ((l.w_force i j).pow 2).mul hw using 1
    · funext t
      field_simp [(q t).z_separation_ne_zero hij]
      linear_combination -(a t ^ 3) * (q t).wForce_sq_zsep_cube_wsep i j hij
    · simp
  have ho : (fun t => (a t / ((q t).z i - (q t).z j)) ^ 3) =o[atTop]
      (fun _ => (1 : ℂ) ^ 3) := by
    simpa only [one_pow] using (isLittleO_one_iff ℂ).mpr hc
  have hquot := ho.of_pow (by decide : (3 : ℕ) ≠ 0)
  exact (hquot.mul_isBigO (isBigO_refl (fun t => (q t).z i - (q t).z j) atTop)).congr
    (fun t => div_mul_cancel₀ _ ((q t).z_separation_ne_zero hij)) (fun t => one_mul _)

theorem w_positions_ne_of_z_separation_bigO_scale
    (hs : ∀ t, a t ≠ 0) (i j : Fin n) (hij : i ≠ j)
    (hz : (fun t => (q t).z i - (q t).z j) =O[atTop] a) :
    l.w.position i ≠ l.w.position j := by
  intro hp
  exact isLittleO_irrefl (Eventually.of_forall hs).frequently
    ((l.scale_littleO_z_separation_of_equal_w_positions i j hij hp).trans_isBigO hz)

theorem z_separation_bigO_scale_of_maximal_w_pair
    (hs : ∀ t, a t ≠ 0) (i j : Fin n) (hij : i ≠ j)
    (hf : l.w.force i j ≠ 0) (hp : l.w.position i ≠ l.w.position j) :
    (fun t => (q t).z i - (q t).z j) =O[atTop] a := by
  have hw : Tendsto (fun t => a t * ((q t).w i - (q t).w j)) atTop
      (𝓝 (l.w.position i - l.w.position j)) := by
    simpa only [mul_sub] using (l.w_position i).sub (l.w_position j)
  have hc : Tendsto (fun t => (((q t).z i - (q t).z j) / a t) ^ 3) atTop
      (𝓝 ((l.w.force i j ^ 2 * (l.w.position i - l.w.position j))⁻¹)) := by
    convert (((l.w_force i j).pow 2).mul hw).inv₀
      (mul_ne_zero (pow_ne_zero 2 hf) (sub_ne_zero.mpr hp)) using 1
    funext t
    apply (mul_right_cancel₀ (mul_ne_zero
      (pow_ne_zero 2 (mul_ne_zero (hs t) ((q t).wForce_ne_zero i j hij)))
      (mul_ne_zero (hs t) ((q t).w_separation_ne_zero hij))))
    rw [inv_mul_cancel₀ (mul_ne_zero
      (pow_ne_zero 2 (mul_ne_zero (hs t) ((q t).wForce_ne_zero i j hij)))
      (mul_ne_zero (hs t) ((q t).w_separation_ne_zero hij)))]
    field_simp [hs t]
    linear_combination (q t).wForce_sq_zsep_cube_wsep i j hij
  have hpow : (fun t => (((q t).z i - (q t).z j) / a t) ^ 3) =O[atTop]
      (fun _ => (1 : ℂ) ^ 3) := by
    simpa only [one_pow] using hc.isBigO_one ℂ
  have hquot := hpow.of_pow (by decide : (3 : ℕ) ≠ 0)
  exact (hquot.mul (isBigO_refl a atTop)).congr
    (fun t => div_mul_cancel₀ _ (hs t)) (fun t => one_mul _)

end ScaledZWLimit
end CentralConfigurations
