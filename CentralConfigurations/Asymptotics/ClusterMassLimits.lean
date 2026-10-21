import CentralConfigurations.Asymptotics.KiteRatioLimits

/-!
# Subleading cluster equations at a double-edge separation

These are consequences of the actual force equations used for the cluster
equations of Section 11.5. A cluster separated in leading w-position has
weighted z-center negligible relative to a double-edge z-separation. Single
w-edges have negligible z-separation on the same scale. In contrast, a single
z-edge cannot have a finite normalized z-separation. All inverse-distance
branches remain those of the given solutions.
-/

namespace CentralConfigurations

open Filter
open scoped Topology BigOperators

theorem OneColorLimit.partial_component_balance {n : ℕ} {mass : Fin n → ℂ}
    (l : OneColorLimit ℂ n mass) (s : Finset (Fin n)) :
    (∑ i ∈ s, mass i * l.position i) =
      ∑ i ∈ s, ∑ j ∈ sᶜ, mass i * mass j * l.force i j := by
  have hint : (∑ i ∈ s, ∑ j ∈ s, mass i * mass j * l.force i j) = 0 :=
    antisymmetric_sum_zero s _ (by
      intro i _ j _
      rw [l.antisymm i j]
      ring)
  calc
    _ = ∑ i ∈ s, ∑ j, mass i * mass j * l.force i j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [l.balance i, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = (∑ i ∈ s, ∑ j ∈ s, mass i * mass j * l.force i j) +
        ∑ i ∈ s, ∑ j ∈ sᶜ, mass i * mass j * l.force i j := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.sum_add_sum_compl s _).symm
    _ = _ := by rw [hint, zero_add]

theorem ZWSystem.partial_mass_center_z {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (s : Finset (Fin n)) :
    (∑ i ∈ s, mass i * q.z i) =
      ∑ i ∈ s, ∑ j ∈ sᶜ, mass i * mass j * q.zForce i j := by
  simpa only [ZWSystem.scaledZ, ZWSystem.zForce, one_mul] using
    (q.scaledZ 1).partial_component_balance s

theorem ZWSystem.zForce_div_zsep {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (r s i j : Fin n) (hrs : r ≠ s) (hij : i ≠ j) :
    q.zForce r s / (q.z i - q.z j) =
      (q.delta r s / q.delta i j) * (q.wForce i j / (q.w r - q.w s)) := by
  have hf : q.zForce r s = q.delta r s / (q.w r - q.w s) :=
    (eq_div_iff (q.w_separation_ne_zero hrs)).mpr (q.zForce_mul_wsep r s hrs)
  have hz : q.z i - q.z j = q.delta i j / q.wForce i j := by
    apply (eq_div_iff (q.wForce_ne_zero i j hij)).mpr
    simpa only [mul_comm] using q.wForce_mul_zsep i j hij
  rw [hf, hz]
  field_simp

theorem ZWSystem.force_ratio_cube_separation {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (r s i j : Fin n) (hrs : r ≠ s) (hij : i ≠ j) :
    q.zForce r s / q.zForce i j =
      (q.wForce r s / q.wForce i j) ^ 3 *
        ((q.z r - q.z s) / (q.z i - q.z j)) ^ 4 := by
  rw [div_pow, div_pow, div_mul_div_comm,
    q.wForce_cube_zsep_four r s hrs, q.wForce_cube_zsep_four i j hij]

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ}
  {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ}
  (l : ScaledZWLimit q a) (hscale : ∀ t, a t ≠ 0)

include hscale

theorem delta_ratio_zero_of_z_force_zero (r s i j : Fin n)
    (hrs : r ≠ s) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j ≠ 0)
    (hrs0 : l.z.force r s = 0) :
    Tendsto (fun t => (q t).delta r s / (q t).delta i j) atTop (𝓝 0) := by
  have hzr := tendsto_ratio_of_scaled hscale hz (l.z_force r s) (l.z_force i j)
  have hwr := tendsto_ratio_of_scaled hscale hw (l.w_force r s) (l.w_force i j)
  rw [hrs0, zero_div] at hzr
  have hfour : Tendsto (fun t => ((q t).delta r s / (q t).delta i j) ^ 4)
      atTop (𝓝 0) := by
    have h := hzr.mul hwr
    simp only [zero_mul] at h
    convert h using 1
    funext t
    exact (q t).delta_ratio_fourth r s i j hrs hij
  apply tendsto_zero_of_square
  apply tendsto_zero_of_square
  simpa only [← pow_mul] using hfour

theorem z_force_div_double_separation_zero
    (ha : Tendsto a atTop (𝓝 0)) (r s i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j ≠ 0)
    (hp : l.w.position r ≠ l.w.position s) :
    Tendsto (fun t => (q t).zForce r s / ((q t).z i - (q t).z j))
      atTop (𝓝 0) := by
  have hrs : r ≠ s := by intro h; exact hp (congrArg l.w.position h)
  have hf : l.z.force r s = 0 := by
    by_contra h
    exact hp (l.z_stroke_w_close ha r s hrs h)
  have hd := l.delta_ratio_zero_of_z_force_zero hscale r s i j hrs hij hz hw hf
  have hsep : Tendsto (fun t => a t * ((q t).w r - (q t).w s))
      atTop (𝓝 (l.w.position r - l.w.position s)) := by
    simpa only [mul_sub] using (l.w_position r).sub (l.w_position s)
  have hratio := tendsto_ratio_of_scaled hscale (sub_ne_zero.mpr hp) (l.w_force i j) hsep
  have h := hd.mul hratio
  simp only [zero_mul] at h
  convert h using 1
  funext t
  exact (q t).zForce_div_zsep r s i j hrs hij

theorem cluster_z_center_div_double_separation_zero
    (ha : Tendsto a atTop (𝓝 0)) (s : Finset (Fin n)) (i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j ≠ 0)
    (hclosed : ∀ r ∈ s, ∀ v ∉ s, l.w.position r ≠ l.w.position v) :
    Tendsto (fun t => (∑ r ∈ s, mass r * (q t).z r) / ((q t).z i - (q t).z j))
      atTop (𝓝 0) := by
  have hterm (r : Fin n) (hr : r ∈ s) (v : Fin n) (hv : v ∈ sᶜ) :
      Tendsto (fun t => mass r * mass v *
        ((q t).zForce r v / ((q t).z i - (q t).z j))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (l.z_force_div_double_separation_zero hscale ha r v i j hij hz hw
        (hclosed r hr v (Finset.mem_compl.mp hv)))
  have h := tendsto_finsetSum s (fun r hr => tendsto_finsetSum sᶜ (hterm r hr))
  simpa only [← mul_div_assoc, ← Finset.sum_div, ← ZWSystem.partial_mass_center_z,
    Finset.sum_const_zero] using h

theorem singleton_z_div_double_separation_zero
    (ha : Tendsto a atTop (𝓝 0)) (r i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j ≠ 0) (hm : mass r ≠ 0)
    (hother : ∀ v, v ≠ r → l.w.position r ≠ l.w.position v) :
    Tendsto (fun t => (q t).z r / ((q t).z i - (q t).z j)) atTop (𝓝 0) := by
  have h := l.cluster_z_center_div_double_separation_zero hscale ha {r} i j hij hz hw (by
    intro v hv w hw
    have hvr : v = r := by simpa only [Finset.mem_singleton] using hv
    subst v
    exact hother w (by simpa only [Finset.mem_singleton] using hw))
  have h' := tendsto_const_nhds.mul h (f := fun _ : ℕ => (mass r)⁻¹)
  simpa [← mul_div_assoc, hm] using h'

theorem single_w_edge_z_separation_ratio_zero (r s i j : Fin n)
    (hrs : r ≠ s) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j ≠ 0)
    (hzrs : l.z.force r s = 0) (hwrs : l.w.force r s ≠ 0) :
    Tendsto (fun t => ((q t).z r - (q t).z s) / ((q t).z i - (q t).z j))
      atTop (𝓝 0) := by
  have hd := l.delta_ratio_zero_of_z_force_zero hscale r s i j hrs hij hz hw hzrs
  have hg := tendsto_ratio_of_scaled hscale hw (l.w_force r s) (l.w_force i j)
  have h := hd.div hg (div_ne_zero hwrs hw)
  simp only [zero_div] at h
  convert h using 1
  funext t
  exact (q t).z_separation_ratio_from_wForce r s i j hrs hij

theorem single_z_edge_no_finite_separation_ratio (r s i j : Fin n)
    (hrs : r ≠ s) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j ≠ 0)
    (hzrs : l.z.force r s ≠ 0) (hwrs : l.w.force r s = 0) (v : ℂ)
    (hv : Tendsto (fun t => ((q t).z r - (q t).z s) / ((q t).z i - (q t).z j))
      atTop (𝓝 v)) : False := by
  have hzlim := tendsto_ratio_of_scaled hscale hz (l.z_force r s) (l.z_force i j)
  have hwlim := tendsto_ratio_of_scaled hscale hw (l.w_force r s) (l.w_force i j)
  rw [hwrs, zero_div] at hwlim
  have h := (hwlim.pow 3).mul (hv.pow 4)
  simp only [zero_pow (by decide : 3 ≠ 0), zero_mul] at h
  have hzero : Tendsto (fun t => (q t).zForce r s / (q t).zForce i j) atTop (𝓝 0) := by
    convert h using 1
    funext t
    exact (q t).force_ratio_cube_separation r s i j hrs hij
  exact (div_ne_zero hzrs hz) (tendsto_nhds_unique hzlim hzero)

end ScaledZWLimit
end CentralConfigurations
