import CentralConfigurations.Model.Torque
import CentralConfigurations.Diagrams.TraceTwo

/-!
# Limit identities for the isolated maximal pair

Analytic inputs for the last assertion of Chang (2023), Theorem 3.3(d).
No principal complex root is selected: inverse-distance ratios are controlled
through their squared identities and the exact torque equation.
-/

namespace CentralConfigurations

open Filter Asymptotics
open scoped Topology

theorem tendsto_ratio_of_scaled {f g a : ℕ → ℂ} {u v : ℂ}
    (ha : ∀ t, a t ≠ 0) (hv : v ≠ 0)
    (hf : Tendsto (fun t => a t * f t) atTop (𝓝 u))
    (hg : Tendsto (fun t => a t * g t) atTop (𝓝 v)) :
    Tendsto (fun t => f t / g t) atTop (𝓝 (u / v)) := by
  have h := hf.div hg hv
  change Tendsto (fun t => (a t * f t) / (a t * g t)) atTop (𝓝 (u / v)) at h
  simpa only [mul_div_mul_left _ _ (ha _)] using h

theorem tendsto_zero_of_square {f : ℕ → ℂ}
    (h : Tendsto (fun t => f t ^ 2) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  have ho : (fun t => f t ^ 2) =o[atTop] (fun _ => (1 : ℂ) ^ 2) := by
    simpa only [one_pow] using (isLittleO_one_iff ℂ).mpr h
  exact (isLittleO_one_iff ℂ).mp (ho.of_pow (by decide : (2 : ℕ) ≠ 0))

theorem PairEstimateData.small_scale_littleO_w_of_absent (p : PairEstimateData)
    (hz : p.zForce =o[atTop] p.scale) :
    (fun t => p.eps t ^ 2) =o[atTop] p.w := by
  have hc : (fun t => (p.w t)⁻¹ ^ 3) =o[atTop] (fun t => p.scale t ^ 3) :=
    ((hz.pow (by decide : 0 < (2 : ℕ))).mul_isBigO p.z_upper).congr
      (fun t => (p.swap.inv_z_cube t).symm) (fun t => by dsimp [PairEstimateData.scale]; ring)
  have hi : (fun t => (p.w t)⁻¹) =o[atTop] p.scale :=
    hc.of_pow (by decide : (3 : ℕ) ≠ 0)
  simpa only [PairEstimateData.scale, inv_pow, inv_inv] using
    hi.inv_rev (Eventually.of_forall fun t h => (inv_ne_zero (p.w_ne_zero t) h).elim)

theorem PairEstimateData.delta_ratio_square (p r : PairEstimateData) (t : ℕ) :
    (p.delta t / r.delta t) ^ 2 = (r.z t * r.w t) / (p.z t * p.w t) := by
  apply (mul_right_cancel₀ (mul_ne_zero (pow_ne_zero 2 (r.delta_ne_zero t))
    (mul_ne_zero (p.z_ne_zero t) (p.w_ne_zero t))))
  field_simp [p.z_ne_zero t, p.w_ne_zero t, r.delta_ne_zero t]
  linear_combination (p.distance_eq t) - (r.distance_eq t)

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))

theorem inverseScale_ne_zero (i j : Fin n) (hij : i ≠ j) (t : ℕ) :
    (q t).inverseScale ≠ 0 := by
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i j hij)))

theorem z_separation_ratio_limit (i j k r : Fin n) (hij : i ≠ j)
    (hkr : l.z.position k ≠ l.z.position r) :
    Tendsto (fun t => ((q t).z i - (q t).z j) / ((q t).z k - (q t).z r)) atTop
      (𝓝 ((l.z.position i - l.z.position j) / (l.z.position k - l.z.position r))) :=
  tendsto_ratio_of_scaled (inverseScale_ne_zero (q := q) i j hij) (sub_ne_zero.mpr hkr)
    (by simpa only [mul_sub] using (l.z_position i).sub (l.z_position j))
    (by simpa only [mul_sub] using (l.z_position k).sub (l.z_position r))

theorem z_position_separation_ratio_limit (i j : Fin n) (hij : i ≠ j)
    (hp : l.z.position i ≠ l.z.position j) :
    Tendsto (fun t => (q t).z i / ((q t).z i - (q t).z j)) atTop
      (𝓝 (l.z.position i / (l.z.position i - l.z.position j))) :=
  tendsto_ratio_of_scaled (inverseScale_ne_zero (q := q) i j hij) (sub_ne_zero.mpr hp)
    (l.z_position i) (by simpa only [mul_sub] using (l.z_position i).sub (l.z_position j))

theorem torqueCorrection_limit (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j : Fin n) (hij : i ≠ j) (hi : l.z.position i ≠ 0) (hj : l.z.position j = 0)
    (hwi : (fun t => (q t).w i) =O[atTop] (fun t => ((q t).epsilon : ℂ) ^ 2))
    (hz : l.z.force i j = 0) :
    Tendsto (fun t => (q t).torqueCorrection i j) atTop (𝓝 (-1)) := by
  let p := ZWSystem.pairEstimateData q hb i j hij
  have hs := p.small_scale_littleO_w_of_absent ((l.pair_z_absent_iff hb i j hij).mpr hz)
  have hw : Tendsto (fun t => (q t).w i / ((q t).w i - (q t).w j)) atTop (𝓝 0) :=
    (hwi.trans_isLittleO hs).tendsto_div_nhds_zero
  have hpi : l.z.position i ≠ l.z.position j := by rwa [hj]
  have hzlim := l.z_position_separation_ratio_limit i j hij hpi
  have h := hw.sub hzlim
  simpa only [← ZWSystem.torqueCorrection_eq _ i j hij, hj, sub_zero,
    div_self hi, zero_sub] using h

theorem w_separation_ratio_limit (i j k r : Fin n) (hij : i ≠ j)
    (hkr : l.w.position k ≠ l.w.position r) :
    Tendsto (fun t => ((q t).w i - (q t).w j) / ((q t).w k - (q t).w r)) atTop
      (𝓝 ((l.w.position i - l.w.position j) / (l.w.position k - l.w.position r))) :=
  tendsto_ratio_of_scaled (inverseScale_ne_zero (q := q) i j hij) (sub_ne_zero.mpr hkr)
    (by simpa only [mul_sub] using (l.w_position i).sub (l.w_position j))
    (by simpa only [mul_sub] using (l.w_position k).sub (l.w_position r))

/-- The farther external bodies contribute negligibly after division by the
inverse distance to the uniquely closer body. -/
theorem delta_ratio_limit_zero (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j k r : Fin n) (hij : i ≠ j) (hkr : k ≠ r)
    (hz : l.z.position i ≠ l.z.position j)
    (hw : l.w.position i ≠ l.w.position j) (hc : l.w.position k = l.w.position r) :
    Tendsto (fun t => (q t).delta i j / (q t).delta k r) atTop (𝓝 0) := by
  have hzr := l.z_separation_ratio_limit k r i j hkr hz
  have hwr := l.w_separation_ratio_limit k r i j hkr hw
  rw [hc, sub_self, zero_div] at hwr
  have hprod := hzr.mul hwr
  simp only [mul_zero] at hprod
  apply tendsto_zero_of_square
  convert hprod using 1
  funext t
  have heq := (ZWSystem.pairEstimateData q hb i j hij).delta_ratio_square
    (ZWSystem.pairEstimateData q hb k r hkr) t
  change ((q t).delta i j / (q t).delta k r) ^ 2 =
    (((q t).z k - (q t).z r) * ((q t).w k - (q t).w r)) /
      (((q t).z i - (q t).z j) * ((q t).w i - (q t).w j)) at heq
  rw [heq]
  change (_ * _) / (_ * _) = _
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem w_separation_ratio_one_of_small
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j k : Fin n) (hjk : j ≠ k)
    (hwi : (fun t => (q t).w i) =O[atTop] (fun t => ((q t).epsilon : ℂ) ^ 2))
    (hwj : (fun t => (q t).w j) =O[atTop] (fun t => ((q t).epsilon : ℂ) ^ 2))
    (hz : l.z.force j k = 0) :
    Tendsto (fun t => ((q t).w i - (q t).w k) / ((q t).w j - (q t).w k))
      atTop (𝓝 1) := by
  let p := ZWSystem.pairEstimateData q hb j k hjk
  have hs := p.small_scale_littleO_w_of_absent ((l.pair_z_absent_iff hb j k hjk).mpr hz)
  have he := ((hwi.sub hwj).trans_isLittleO hs).tendsto_div_nhds_zero
  have hlim := he.add_const (1 : ℂ)
  simp only [zero_add] at hlim
  convert hlim using 1
  funext t
  change ((q t).w i - (q t).w k) / ((q t).w j - (q t).w k) =
    ((q t).w i - (q t).w j) / ((q t).w j - (q t).w k) + 1
  field_simp [(q t).w_separation_ne_zero hjk]
  ring

end ScaledZWLimit
end CentralConfigurations
