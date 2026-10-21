import CentralConfigurations.FiveBody.D5Support
import CentralConfigurations.FiveBody.D5ThreeBlock
import CentralConfigurations.Diagrams.BoundaryCuts

namespace CentralConfigurations.FiveBody.D5
open Filter Asymptotics
open scoped Topology BigOperators

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass} {s r : ℕ → ℂ}

/-- Two independently normalized position limits of the same actual solutions. -/
structure PositionLimit (q : ℕ → ZWSystem ℂ 5 mass) (s r : ℕ → ℂ) where
  z : Fin 5 → ℂ
  w : Fin 5 → ℂ
  zlim : ∀ i, Tendsto (fun t => (q t).z i / s t) atTop (𝓝 (z i))
  wlim : ∀ i, Tendsto (fun t => (q t).w i / r t) atTop (𝓝 (w i))

theorem zw_potential (p : ZWSystem ℂ 5 mass) :
    p.toNormalized.potential = ∑ i, mass i * p.z i * p.w i := by
  rw [p.toNormalized.potential_eq_inertia]
  unfold NormalizedSystem.inertia
  apply Finset.sum_congr rfl
  intro i _
  have h := inverse_zw_separation (p.z i) (p.w i) 0 0
  simp only [add_zero,zero_sub,sub_zero,mul_zero,zero_div] at h
  change mass i * (((p.z i+p.w i)/2)^2 + (Complex.I*(p.w i-p.z i)/2)^2) = _
  rw [h]
  ring

namespace PositionLimit
variable (L : PositionLimit q s r)

theorem center_z : ∑ i, mass i * L.z i = 0 := by
  have h := tendsto_finset_sum Finset.univ (fun i _ => (L.zlim i).const_mul (mass i))
  have heq t : (∑ i, mass i * ((q t).z i / s t)) = 0 := by
    simp only [← mul_div_assoc, ← Finset.sum_div, (q t).mass_center_z, zero_div]
  exact tendsto_nhds_unique (h.congr (fun t => heq t)) tendsto_const_nhds

theorem center_w : ∑ i, mass i * L.w i = 0 := by
  have h := tendsto_finset_sum Finset.univ (fun i _ => (L.wlim i).const_mul (mass i))
  have heq t : (∑ i, mass i * ((q t).w i / r t)) = 0 := by
    simp only [← mul_div_assoc, ← Finset.sum_div, (q t).mass_center_w, zero_div]
  exact tendsto_nhds_unique (h.congr (fun t => heq t)) tendsto_const_nhds

theorem inertia_zero {I : ℂ} (hI : ∀ t, (q t).toNormalized.potential=I)
    (hprod : Tendsto (fun t => (s t*r t)⁻¹) atTop (𝓝 0)) :
    ∑ i, mass i * L.z i * L.w i = 0 := by
  have h := tendsto_finset_sum Finset.univ
    (fun i _ => ((L.zlim i).const_mul (mass i)).mul (L.wlim i))
  have heq t : (∑ i, mass i*((q t).z i/s t)*((q t).w i/r t)) = I*(s t*r t)⁻¹ := by
    calc
      _ = (∑ i, mass i*(q t).z i*(q t).w i)/(s t*r t) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [← zw_potential, hI]; rfl
  have hz : Tendsto (fun t => I*(s t*r t)⁻¹) atTop (𝓝 0) := by simpa using hprod.const_mul I
  exact tendsto_nhds_unique (h.congr heq) hz

theorem delta_zero (hs : ∀ t, s t ≠ 0) (hr : ∀ t, r t ≠ 0)
    (hprod : Tendsto (fun t => (s t*r t)⁻¹) atTop (𝓝 0))
    (i j : Fin 5) (hmetric : (L.z i-L.z j)*(L.w i-L.w j) ≠ 0) :
    Tendsto (fun t => (q t).delta i j) atTop (𝓝 0) := by
  have hij : i ≠ j := by intro h; subst j; simp at hmetric
  have hm := ((L.zlim i).sub (L.zlim j)).mul ((L.wlim i).sub (L.wlim j))
  have hh := hprod.div hm hmetric
  apply D9.zero_of_power (n := 2) (by decide)
  have heq t : (s t*r t)⁻¹ / (((q t).z i/s t-(q t).z j/s t)*
      ((q t).w i/r t-(q t).w j/r t)) = (q t).delta i j^2 := by
    rw [← sub_div, ← sub_div, div_mul_div_comm]
    have hsep : ((q t).z i-(q t).z j)*((q t).w i-(q t).w j) ≠ 0 :=
      mul_ne_zero ((q t).z_separation_ne_zero hij) ((q t).w_separation_ne_zero hij)
    rw [div_div_eq_mul_div,inv_mul_cancel₀ (mul_ne_zero (hs t) (hr t))]
    symm
    exact (eq_div_iff hsep).mpr ((q t).distance i j hij)
  simpa only [zero_div] using hh.congr heq

theorem force_z_zero (hs : ∀ t, s t ≠ 0) (hr : ∀ t, r t ≠ 0)
    (hprod : Tendsto (fun t => (s t*r t)⁻¹) atTop (𝓝 0))
    (i j : Fin 5) (hmetric : (L.z i-L.z j)*(L.w i-L.w j) ≠ 0) :
    Tendsto (fun t => (q t).zForce i j/s t) atTop (𝓝 0) := by
  have h := ((L.delta_zero hs hr hprod i j hmetric).pow 3).mul ((L.zlim i).sub (L.zlim j))
  simp only [zero_pow (by decide : 3 ≠ 0),zero_mul] at h
  convert h using 1
  funext t
  dsimp [ZWSystem.zForce]
  ring

theorem force_w_zero (hs : ∀ t, s t ≠ 0) (hr : ∀ t, r t ≠ 0)
    (hprod : Tendsto (fun t => (s t*r t)⁻¹) atTop (𝓝 0))
    (i j : Fin 5) (hmetric : (L.z i-L.z j)*(L.w i-L.w j) ≠ 0) :
    Tendsto (fun t => (q t).wForce i j/r t) atTop (𝓝 0) := by
  have h := ((L.delta_zero hs hr hprod i j hmetric).pow 3).mul ((L.wlim i).sub (L.wlim j))
  simp only [zero_pow (by decide : 3 ≠ 0),zero_mul] at h
  convert h using 1
  funext t
  dsimp [ZWSystem.wForce]
  ring

/-- Exact cancellation of internal forces works for any of the three blocks. -/
theorem isolated_block_z (hs : ∀ t, s t ≠ 0) (hr : ∀ t, r t ≠ 0)
    (hprod : Tendsto (fun t => (s t*r t)⁻¹) atTop (𝓝 0))
    (A : Finset (Fin 5))
    (hA : ∀ i∈A, ∀ j∈Aᶜ, (L.z i-L.z j)*(L.w i-L.w j) ≠ 0) :
    ∑ i∈A, mass i * L.z i = 0 := by
  classical
  have hl := tendsto_finset_sum A (fun i _ => (L.zlim i).const_mul (mass i))
  have hb := tendsto_finset_sum (A ×ˢ Aᶜ) (fun ij hij =>
    (L.force_z_zero hs hr hprod ij.1 ij.2
      (hA ij.1 (Finset.mem_product.mp hij).1 ij.2 (Finset.mem_product.mp hij).2)).const_mul (mass ij.1*mass ij.2))
  have heq t : (∑ i∈A, mass i*((q t).z i/s t)) =
      ∑ ij∈A ×ˢ Aᶜ, mass ij.1*mass ij.2*((q t).zForce ij.1 ij.2/s t) := by
    simpa only [ZWSystem.scaledZ,ZWSystem.zForce,div_eq_mul_inv,mul_comm (s t)⁻¹, mul_assoc] using
      ((q t).scaledZ (s t)⁻¹).boundary_balance A
  have hh := hl.congr heq
  simpa only [mul_zero,Finset.sum_const_zero] using tendsto_nhds_unique hh hb

theorem isolated_block_w (hs : ∀ t, s t ≠ 0) (hr : ∀ t, r t ≠ 0)
    (hprod : Tendsto (fun t => (s t*r t)⁻¹) atTop (𝓝 0))
    (A : Finset (Fin 5))
    (hA : ∀ i∈A, ∀ j∈Aᶜ, (L.z i-L.z j)*(L.w i-L.w j) ≠ 0) :
    ∑ i∈A, mass i * L.w i = 0 := by
  classical
  have hl := tendsto_finset_sum A (fun i _ => (L.wlim i).const_mul (mass i))
  have hb := tendsto_finset_sum (A ×ˢ Aᶜ) (fun ij hij =>
    (L.force_w_zero hs hr hprod ij.1 ij.2
      (hA ij.1 (Finset.mem_product.mp hij).1 ij.2 (Finset.mem_product.mp hij).2)).const_mul (mass ij.1*mass ij.2))
  have heq t : (∑ i∈A, mass i*((q t).w i/r t)) =
      ∑ ij∈A ×ˢ Aᶜ, mass ij.1*mass ij.2*((q t).wForce ij.1 ij.2/r t) := by
    simpa only [ZWSystem.scaledZ,ZWSystem.swap,ZWSystem.zForce,ZWSystem.wForce,
      div_eq_mul_inv,mul_comm (r t)⁻¹,mul_assoc] using
      ((q t).swap.scaledZ (r t)⁻¹).boundary_balance A
  have hh := hl.congr heq
  simpa only [mul_zero,Finset.sum_const_zero] using tendsto_nhds_unique hh hb

end PositionLimit
end CentralConfigurations.FiveBody.D5
