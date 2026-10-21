import CentralConfigurations.Asymptotics.FourthPowerExtraction
import CentralConfigurations.Asymptotics.TorqueLimits

/-!
# Branch-preserving triangle ratios from actual force equations

The two colors have the same limiting force ratios at two closed uncircled
rows. Force products give fourth powers of inverse-distance ratios. Compact
extraction retains their actual branches, and the exact separation triangle
gives the final linear relation between the two roots.
-/

namespace CentralConfigurations

open Filter
open scoped Topology

namespace ZWSystem

variable {n : ℕ} {mass : Fin n → ℂ} (q : ZWSystem ℂ n mass)

theorem delta_ne_zero (i j : Fin n) (hij : i ≠ j) : q.delta i j ≠ 0 := by
  intro h
  have he := q.distance i j hij
  simp [h] at he

theorem zForce_ne_zero (i j : Fin n) (hij : i ≠ j) : q.zForce i j ≠ 0 :=
  mul_ne_zero (pow_ne_zero 3 (q.delta_ne_zero i j hij)) (q.z_separation_ne_zero hij)

theorem wForce_ne_zero (i j : Fin n) (hij : i ≠ j) : q.wForce i j ≠ 0 :=
  mul_ne_zero (pow_ne_zero 3 (q.delta_ne_zero i j hij)) (q.w_separation_ne_zero hij)

theorem force_product (i j : Fin n) (hij : i ≠ j) :
    q.zForce i j * q.wForce i j = q.delta i j ^ 4 := by
  calc
    _ = q.delta i j ^ 4 * (q.delta i j ^ 2 * ((q.z i - q.z j) * (q.w i - q.w j))) := by
      dsimp [zForce, wForce]
      ring
    _ = _ := by rw [q.distance i j hij]; ring

theorem wForce_mul_zsep (i j : Fin n) (hij : i ≠ j) :
    q.wForce i j * (q.z i - q.z j) = q.delta i j := by
  calc
    _ = q.delta i j * (q.delta i j ^ 2 * ((q.z i - q.z j) * (q.w i - q.w j))) := by
      dsimp [wForce]
      ring
    _ = _ := by rw [q.distance i j hij]; ring

theorem delta_ratio_fourth (i j k r : Fin n) (hij : i ≠ j) (hkr : k ≠ r) :
    (q.delta i j / q.delta k r) ^ 4 =
      (q.zForce i j / q.zForce k r) * (q.wForce i j / q.wForce k r) := by
  rw [div_mul_div_comm, q.force_product i j hij, q.force_product k r hkr, div_pow]

theorem z_separation_ratio_from_wForce (i j k r : Fin n) (hij : i ≠ j) (hkr : k ≠ r) :
    (q.z i - q.z j) / (q.z k - q.z r) =
      (q.delta i j / q.delta k r) / (q.wForce i j / q.wForce k r) := by
  have h1 : q.z i - q.z j = q.delta i j / q.wForce i j := by
    apply (eq_div_iff (q.wForce_ne_zero i j hij)).mpr
    simpa only [mul_comm] using q.wForce_mul_zsep i j hij
  have h2 : q.z k - q.z r = q.delta k r / q.wForce k r := by
    apply (eq_div_iff (q.wForce_ne_zero k r hkr)).mpr
    simpa only [mul_comm] using q.wForce_mul_zsep k r hkr
  rw [h1, h2]
  field_simp

end ZWSystem

theorem triangle_force_ratio_roots {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u v : ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hzik : Tendsto (fun t => (q t).zForce i k / (q t).zForce i j) atTop (𝓝 u))
    (hwik : Tendsto (fun t => (q t).wForce i k / (q t).wForce i j) atTop (𝓝 u))
    (hzjk : Tendsto (fun t => (q t).zForce j k / (q t).zForce i j) atTop (𝓝 v))
    (hwjk : Tendsto (fun t => (q t).wForce j k / (q t).wForce i j) atTop (𝓝 v)) :
    ∃ x y : ℂ, x ^ 4 = u ^ 2 ∧ y ^ 4 = v ^ 2 ∧ x / u = 1 + y / v := by
  have hpow (r s : Fin n) (hrs : r ≠ s) (w : ℂ)
      (hz : Tendsto (fun t => (q t).zForce r s / (q t).zForce i j) atTop (𝓝 w))
      (hw : Tendsto (fun t => (q t).wForce r s / (q t).wForce i j) atTop (𝓝 w)) :
      Tendsto (fun t => ((q t).delta r s / (q t).delta i j) ^ 4) atTop (𝓝 (w ^ 2)) := by
    have h := hz.mul hw
    have he : (fun t => ((q t).zForce r s / (q t).zForce i j) *
        ((q t).wForce r s / (q t).wForce i j)) =
        (fun t => ((q t).delta r s / (q t).delta i j) ^ 4) :=
      funext fun t => ((q t).delta_ratio_fourth r s i j hrs hij).symm
    rw [he] at h
    simpa only [pow_two] using h
  obtain ⟨x, y, φ, hφ, hx, hy, hx4, hy4⟩ := exists_simultaneous_fourth_power_limits
    (hpow i k hik u hzik hwik) (hpow j k hjk v hzjk hwjk)
  have hxs : Tendsto (fun t => ((q (φ t)).z i - (q (φ t)).z k) /
      ((q (φ t)).z i - (q (φ t)).z j)) atTop (𝓝 (x / u)) := by
    convert hx.div (hwik.comp hφ.tendsto_atTop) hu using 1
    funext t
    exact (q (φ t)).z_separation_ratio_from_wForce i k i j hik hij
  have hys : Tendsto (fun t => ((q (φ t)).z j - (q (φ t)).z k) /
      ((q (φ t)).z i - (q (φ t)).z j)) atTop (𝓝 (y / v)) := by
    convert hy.div (hwjk.comp hφ.tendsto_atTop) hv using 1
    funext t
    exact (q (φ t)).z_separation_ratio_from_wForce j k i j hjk hij
  have he (t : ℕ) : ((q (φ t)).z i - (q (φ t)).z k) /
      ((q (φ t)).z i - (q (φ t)).z j) =
      1 + ((q (φ t)).z j - (q (φ t)).z k) /
        ((q (φ t)).z i - (q (φ t)).z j) := by
    field_simp [(q (φ t)).z_separation_ne_zero hij]
    ring
  simp_rw [he] at hxs
  exact ⟨x, y, hx4, hy4, tendsto_nhds_unique hxs (tendsto_const_nhds.add hys)⟩

end CentralConfigurations
