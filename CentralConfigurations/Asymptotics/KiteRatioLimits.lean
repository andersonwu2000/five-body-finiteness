import CentralConfigurations.Asymptotics.TriangleRatioLimits

/-!
# Both separation triangles with different color force ratios

The kite cases have different ratios in the two colors. A common subsequence
of the actual inverse-distance ratios preserves both separation identities.
-/

namespace CentralConfigurations

open Filter
open scoped Topology

theorem ZWSystem.zForce_mul_wsep {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) :
    q.zForce i j * (q.w i - q.w j) = q.delta i j := by
  calc
    _ = q.delta i j * (q.delta i j ^ 2 * ((q.z i - q.z j) * (q.w i - q.w j))) := by
      dsimp [ZWSystem.zForce]
      ring
    _ = _ := by rw [q.distance i j hij]; ring

theorem ZWSystem.w_separation_ratio_from_zForce {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j k r : Fin n) (hij : i ≠ j) (hkr : k ≠ r) :
    (q.w i - q.w j) / (q.w k - q.w r) =
      (q.delta i j / q.delta k r) / (q.zForce i j / q.zForce k r) := by
  have h1 : q.w i - q.w j = q.delta i j / q.zForce i j := by
    apply (eq_div_iff (q.zForce_ne_zero i j hij)).mpr
    simpa only [mul_comm] using q.zForce_mul_wsep i j hij
  have h2 : q.w k - q.w r = q.delta k r / q.zForce k r := by
    apply (eq_div_iff (q.zForce_ne_zero k r hkr)).mpr
    simpa only [mul_comm] using q.zForce_mul_wsep k r hkr
  rw [h1, h2]
  field_simp

theorem two_color_triangle_force_ratio_roots {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (u v U V : ℂ) (hu : u ≠ 0) (hv : v ≠ 0) (hU : U ≠ 0) (hV : V ≠ 0)
    (hzik : Tendsto (fun t => (q t).zForce i k / (q t).zForce i j) atTop (𝓝 u))
    (hwik : Tendsto (fun t => (q t).wForce i k / (q t).wForce i j) atTop (𝓝 U))
    (hzjk : Tendsto (fun t => (q t).zForce j k / (q t).zForce i j) atTop (𝓝 v))
    (hwjk : Tendsto (fun t => (q t).wForce j k / (q t).wForce i j) atTop (𝓝 V)) :
    ∃ x y : ℂ, x ^ 4 = u * U ∧ y ^ 4 = v * V ∧
      x / U = 1 + y / V ∧ x / u = 1 + y / v := by
  have hpow (r s : Fin n) (hrs : r ≠ s) (w W : ℂ)
      (hz : Tendsto (fun t => (q t).zForce r s / (q t).zForce i j) atTop (𝓝 w))
      (hw : Tendsto (fun t => (q t).wForce r s / (q t).wForce i j) atTop (𝓝 W)) :
      Tendsto (fun t => ((q t).delta r s / (q t).delta i j) ^ 4) atTop (𝓝 (w * W)) := by
    have h := hz.mul hw
    have he : (fun t => ((q t).zForce r s / (q t).zForce i j) *
        ((q t).wForce r s / (q t).wForce i j)) =
        (fun t => ((q t).delta r s / (q t).delta i j) ^ 4) :=
      funext fun t => ((q t).delta_ratio_fourth r s i j hrs hij).symm
    rw [he] at h
    exact h
  obtain ⟨x, y, φ, hφ, hx, hy, hx4, hy4⟩ := exists_simultaneous_fourth_power_limits
    (hpow i k hik u U hzik hwik) (hpow j k hjk v V hzjk hwjk)
  have hxs : Tendsto (fun t => ((q (φ t)).z i - (q (φ t)).z k) /
      ((q (φ t)).z i - (q (φ t)).z j)) atTop (𝓝 (x / U)) := by
    convert hx.div (hwik.comp hφ.tendsto_atTop) hU using 1
    funext t
    exact (q (φ t)).z_separation_ratio_from_wForce i k i j hik hij
  have hys : Tendsto (fun t => ((q (φ t)).z j - (q (φ t)).z k) /
      ((q (φ t)).z i - (q (φ t)).z j)) atTop (𝓝 (y / V)) := by
    convert hy.div (hwjk.comp hφ.tendsto_atTop) hV using 1
    funext t
    exact (q (φ t)).z_separation_ratio_from_wForce j k i j hjk hij
  have hxt : Tendsto (fun t => ((q (φ t)).w i - (q (φ t)).w k) /
      ((q (φ t)).w i - (q (φ t)).w j)) atTop (𝓝 (x / u)) := by
    convert hx.div (hzik.comp hφ.tendsto_atTop) hu using 1
    funext t
    exact (q (φ t)).w_separation_ratio_from_zForce i k i j hik hij
  have hyt : Tendsto (fun t => ((q (φ t)).w j - (q (φ t)).w k) /
      ((q (φ t)).w i - (q (φ t)).w j)) atTop (𝓝 (y / v)) := by
    convert hy.div (hzjk.comp hφ.tendsto_atTop) hv using 1
    funext t
    exact (q (φ t)).w_separation_ratio_from_zForce j k i j hjk hij
  have hez (t : ℕ) : ((q (φ t)).z i - (q (φ t)).z k) /
      ((q (φ t)).z i - (q (φ t)).z j) =
      1 + ((q (φ t)).z j - (q (φ t)).z k) /
        ((q (φ t)).z i - (q (φ t)).z j) := by
    field_simp [(q (φ t)).z_separation_ne_zero hij]
    ring
  have hew (t : ℕ) : ((q (φ t)).w i - (q (φ t)).w k) /
      ((q (φ t)).w i - (q (φ t)).w j) =
      1 + ((q (φ t)).w j - (q (φ t)).w k) /
        ((q (φ t)).w i - (q (φ t)).w j) := by
    field_simp [(q (φ t)).w_separation_ne_zero hij]
    ring
  simp_rw [hez] at hxs
  simp_rw [hew] at hxt
  exact ⟨x, y, hx4, hy4, tendsto_nhds_unique hxs (tendsto_const_nhds.add hys),
    tendsto_nhds_unique hxt (tendsto_const_nhds.add hyt)⟩

end CentralConfigurations
