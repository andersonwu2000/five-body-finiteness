import CentralConfigurations.Asymptotics.ClusterMassLimits

/-!
# Cluster equations relative to any z-stroke

The reference edge need not have a w-stroke. These estimates supply the
subleading cluster equations also for the purely single-color triangles in
Section 11.5. Powers of exact force identities avoid choosing complex roots.
-/

namespace CentralConfigurations

open Filter Asymptotics
open scoped Topology BigOperators

theorem tendsto_zero_of_complex_power {f : ℕ → ℂ} {d : ℕ} (hd : d ≠ 0)
    (h : Tendsto (fun t => f t ^ d) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  have ho : (fun t => f t ^ d) =o[atTop] (fun _ => (1 : ℂ) ^ d) := by
    simpa only [one_pow] using (isLittleO_one_iff ℂ).mpr h
  exact (isLittleO_one_iff ℂ).mp (ho.of_pow hd)

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
  {a : ℕ → ℂ} (l : ScaledZWLimit q a) (hscale : ∀ t, a t ≠ 0)

include hscale

theorem scale_div_z_stroke_separation_zero (ha : Tendsto a atTop (𝓝 0))
    (i j : Fin n) (hij : i ≠ j) (hz : l.z.force i j ≠ 0) :
    Tendsto (fun t => a t / ((q t).z i - (q t).z j)) atTop (𝓝 0) := by
  have h := ((ha.pow 2).mul ((l.w_force i j).pow 3)).div (l.z_force i j) hz
  simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, zero_div] at h
  apply tendsto_zero_of_complex_power (by decide : (4 : ℕ) ≠ 0)
  convert h using 1
  funext t
  change (a t / ((q t).z i - (q t).z j)) ^ 4 =
    a t ^ 2 * (a t * (q t).wForce i j) ^ 3 / (a t * (q t).zForce i j)
  rw [← (q t).wForce_cube_zsep_four i j hij]
  field_simp [hscale t, (q t).wForce_ne_zero i j hij, (q t).z_separation_ne_zero hij]

theorem z_force_div_stroke_separation_zero
    (ha : Tendsto a atTop (𝓝 0)) (r s i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) (hp : l.w.position r ≠ l.w.position s) :
    Tendsto (fun t => (q t).zForce r s / ((q t).z i - (q t).z j))
      atTop (𝓝 0) := by
  have hrs : r ≠ s := by intro h; exact hp (congrArg l.w.position h)
  have hsep : Tendsto (fun t => a t * ((q t).w r - (q t).w s))
      atTop (𝓝 (l.w.position r - l.w.position s)) := by
    simpa only [mul_sub] using (l.w_position r).sub (l.w_position s)
  have hdiff := sub_ne_zero.mpr hp
  have hdelta := tendsto_ratio_of_scaled hscale hdiff (l.w_force r s) hsep
  have hsmall := l.scale_div_z_stroke_separation_zero hscale ha i j hij hz
  have h := (hdelta.div (hsep.pow 3) (pow_ne_zero 3 hdiff)).mul (hsmall.pow 3)
  simp only [zero_pow (by decide : 3 ≠ 0), mul_zero] at h
  apply tendsto_zero_of_complex_power (by decide : (3 : ℕ) ≠ 0)
  convert h using 1
  funext t
  have hf : (q t).zForce r s = (q t).delta r s / ((q t).w r - (q t).w s) :=
    (eq_div_iff ((q t).w_separation_ne_zero hrs)).mpr ((q t).zForce_mul_wsep r s hrs)
  rw [hf]
  dsimp [ZWSystem.wForce]
  field_simp [hscale t, (q t).w_separation_ne_zero hrs, (q t).z_separation_ne_zero hij]

theorem cluster_z_center_div_stroke_separation_zero
    (ha : Tendsto a atTop (𝓝 0)) (s : Finset (Fin n)) (i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0)
    (hclosed : ∀ r ∈ s, ∀ v ∉ s, l.w.position r ≠ l.w.position v) :
    Tendsto (fun t => (∑ r ∈ s, mass r * (q t).z r) / ((q t).z i - (q t).z j))
      atTop (𝓝 0) := by
  have hterm (r : Fin n) (hr : r ∈ s) (v : Fin n) (hv : v ∈ sᶜ) :
      Tendsto (fun t => mass r * mass v *
        ((q t).zForce r v / ((q t).z i - (q t).z j))) atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (l.z_force_div_stroke_separation_zero hscale ha r v i j hij hz
        (hclosed r hr v (Finset.mem_compl.mp hv)))
  have h := tendsto_finsetSum s (fun r hr => tendsto_finsetSum sᶜ (hterm r hr))
  simpa only [← mul_div_assoc, ← Finset.sum_div, ← ZWSystem.partial_mass_center_z,
    Finset.sum_const_zero] using h

theorem singleton_z_div_stroke_separation_zero
    (ha : Tendsto a atTop (𝓝 0)) (r i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) (hm : mass r ≠ 0)
    (hother : ∀ v, v ≠ r → l.w.position r ≠ l.w.position v) :
    Tendsto (fun t => (q t).z r / ((q t).z i - (q t).z j)) atTop (𝓝 0) := by
  have h := l.cluster_z_center_div_stroke_separation_zero hscale ha {r} i j hij hz (by
    intro v hv w hw
    have hvr : v = r := by simpa only [Finset.mem_singleton] using hv
    subst v
    exact hother w (by simpa only [Finset.mem_singleton] using hw))
  have h' := tendsto_const_nhds.mul h (f := fun _ : ℕ => (mass r)⁻¹)
  simpa [← mul_div_assoc, hm] using h'

theorem single_w_edge_z_separation_ratio_to_z_stroke_zero (r s i j : Fin n)
    (hrs : r ≠ s) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0)
    (hzrs : l.z.force r s = 0) (hwrs : l.w.force r s ≠ 0) :
    Tendsto (fun t => ((q t).z r - (q t).z s) / ((q t).z i - (q t).z j))
      atTop (𝓝 0) := by
  have hf := tendsto_ratio_of_scaled hscale hz (l.z_force r s) (l.z_force i j)
  have hg := tendsto_ratio_of_scaled hscale hwrs (l.w_force i j) (l.w_force r s)
  rw [hzrs, zero_div] at hf
  have h := hf.mul (hg.pow 3)
  simp only [zero_mul] at h
  apply tendsto_zero_of_complex_power (by decide : (4 : ℕ) ≠ 0)
  convert h using 1
  funext t
  rw [← (q t).wForce_cube_zsep_four r s hrs,
    ← (q t).wForce_cube_zsep_four i j hij]
  field_simp [(q t).wForce_ne_zero r s hrs, (q t).wForce_ne_zero i j hij,
    (q t).z_separation_ne_zero hij]

end ScaledZWLimit
end CentralConfigurations
