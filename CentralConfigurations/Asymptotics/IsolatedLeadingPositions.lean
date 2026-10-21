import CentralConfigurations.Asymptotics.AttachmentGeometry

/-!
# Isolated leading positions and the opposite small scale

For the cluster equations used in Section 11.5, distinct leading
w-positions bound the actual z-force by the normalization scale. A
singleton leading w-position therefore bounds its entire z-position.
Two z-positions on that scale must have a leading w-edge, by the exact
distance identity. No relative order table or complex root is chosen.
-/

namespace CentralConfigurations

open Filter Asymptotics
open scoped Topology BigOperators

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
  {a : ℕ → ℂ} (l : ScaledZWLimit q a)

/-- The normalized cube has an ordinary limit, even when its cube root
does not. This is sufficient for the force bound. -/
theorem zForce_bigO_scale_of_distinct_w_positions
    (hs : ∀ t, a t ≠ 0) (i j : Fin n)
    (hp : l.w.position i ≠ l.w.position j) :
    (fun t => (q t).zForce i j) =O[atTop] a := by
  have hij : i ≠ j := fun h => hp (congrArg l.w.position h)
  have hw : Tendsto (fun t => a t * ((q t).w i - (q t).w j)) atTop
      (𝓝 (l.w.position i - l.w.position j)) := by
    simpa only [mul_sub] using (l.w_position i).sub (l.w_position j)
  have hf := (l.w_force i j).div (hw.pow 4) (pow_ne_zero 4 (sub_ne_zero.mpr hp))
  have hc : Tendsto (fun t => ((q t).zForce i j / a t) ^ 3) atTop
      (𝓝 (l.w.force i j / (l.w.position i - l.w.position j) ^ 4)) := by
    convert hf using 1
    funext t
    have hid := (q t).swap.wForce_cube_zsep_four i j hij
    change (q t).zForce i j ^ 3 * ((q t).w i - (q t).w j) ^ 4 = (q t).wForce i j at hid
    calc
      ((q t).zForce i j / a t) ^ 3 =
          ((q t).zForce i j ^ 3 * ((q t).w i - (q t).w j) ^ 4) /
            (a t ^ 3 * ((q t).w i - (q t).w j) ^ 4) := by
        field_simp [hs t, (q t).w_separation_ne_zero hij]
      _ = (q t).wForce i j / (a t ^ 3 * ((q t).w i - (q t).w j) ^ 4) := by rw [hid]
      _ = (a t * (q t).wForce i j) / (a t * ((q t).w i - (q t).w j)) ^ 4 := by
        field_simp [hs t, (q t).w_separation_ne_zero hij]
  have hpow : (fun t => ((q t).zForce i j / a t) ^ 3) =O[atTop]
      (fun _ => (1 : ℂ) ^ 3) := by
    simpa only [one_pow] using (hc.isBigO_one ℂ :
      (fun t => ((q t).zForce i j / a t) ^ 3) =O[atTop] (fun _ => (1 : ℂ)))
  have hquot : (fun t => (q t).zForce i j / a t) =O[atTop] (fun _ => (1 : ℂ)) :=
    hpow.of_pow (by decide : (3 : ℕ) ≠ 0)
  exact (hquot.mul (isBigO_refl a atTop)).congr
    (fun t => div_mul_cancel₀ _ (hs t)) (fun t => one_mul (a t))

theorem z_position_bigO_scale_of_isolated_w_position
    (hs : ∀ t, a t ≠ 0) (i : Fin n)
    (hi : ∀ j, j ≠ i → l.w.position i ≠ l.w.position j) :
    (fun t => (q t).z i) =O[atTop] a := by
  apply ZWSystem.w_position_bigO_of_forces (fun t => (q t).swap) a i
  intro j
  change (fun t => (q t).zForce i j) =O[atTop] a
  by_cases hj : j = i
  · subst j
    simpa only [ZWSystem.zForce, sub_self, mul_zero] using (isBigO_zero a atTop)
  · exact l.zForce_bigO_scale_of_distinct_w_positions hs i j (hi j hj)

/-- A separation bounded by the normalization scale forces a nonzero
leading opposite force. The proof uses the squared inverse-distance
identity, so it has no root or phase assumptions. -/
theorem w_force_ne_zero_of_z_separation_bigO_scale
    (hs : ∀ t, a t ≠ 0) (i j : Fin n) (hij : i ≠ j)
    (hz : (fun t => (q t).z i - (q t).z j) =O[atTop] a) :
    l.w.force i j ≠ 0 := by
  intro hzero
  have hf : (fun t => a t * (q t).wForce i j) =o[atTop] (fun _ => (1 : ℂ)) := by
    apply (isLittleO_one_iff ℂ).mpr
    simpa only [hzero] using l.w_force i j
  have hw : (fun t => a t * ((q t).w i - (q t).w j)) =O[atTop] (fun _ => (1 : ℂ)) := by
    apply Filter.Tendsto.isBigO_one
    simpa only [mul_sub] using (l.w_position i).sub (l.w_position j)
  have hp := (((hf.pow (by decide : 0 < 2)).mul_isBigO (hz.pow 3)).mul_isBigO hw)
  have hself : (fun t => a t ^ 3) =o[atTop] (fun t => a t ^ 3) := by
    refine hp.congr (fun t => ?_) (fun t => by ring)
    have hid : (q t).wForce i j ^ 2 * ((q t).z i - (q t).z j) ^ 3 *
        ((q t).w i - (q t).w j) = 1 := by
      calc
        _ = ((q t).delta i j ^ 2 * (((q t).z i - (q t).z j) * ((q t).w i - (q t).w j))) ^ 3 := by
          dsimp [ZWSystem.wForce]
          ring
        _ = 1 := by rw [(q t).distance i j hij]; ring
    calc
      _ = a t ^ 3 * ((q t).wForce i j ^ 2 * ((q t).z i - (q t).z j) ^ 3 *
          ((q t).w i - (q t).w j)) := by ring
      _ = a t ^ 3 := by rw [hid, mul_one]
  exact isLittleO_irrefl (Eventually.of_forall (fun t => pow_ne_zero 3 (hs t))).frequently hself

theorem w_force_ne_zero_between_isolated_w_positions
    (hs : ∀ t, a t ≠ 0) (i j : Fin n) (hij : i ≠ j)
    (hi : ∀ k, k ≠ i → l.w.position i ≠ l.w.position k)
    (hj : ∀ k, k ≠ j → l.w.position j ≠ l.w.position k) :
    l.w.force i j ≠ 0 :=
  l.w_force_ne_zero_of_z_separation_bigO_scale hs i j hij
    ((l.z_position_bigO_scale_of_isolated_w_position hs i hi).sub
      (l.z_position_bigO_scale_of_isolated_w_position hs j hj))

end ScaledZWLimit
end CentralConfigurations
