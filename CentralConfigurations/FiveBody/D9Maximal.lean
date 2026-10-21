import CentralConfigurations.FiveBody.D9Sequence
import CentralConfigurations.FiveBody.D9Mass

namespace CentralConfigurations.FiveBody.D9
open Filter Asymptotics
open scoped Topology BigOperators

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}

theorem outer_cube_limit (hP : mass 3 + mass 4 ≠ 0)
    (h3 : ∀ i : Fin 5, i.val < 3 →
      Tendsto (fun t => (q t).zForce 3 i / ((q t).z 3 - (q t).z 4)) atTop (𝓝 0))
    (h4 : ∀ i : Fin 5, i.val < 3 →
      Tendsto (fun t => (q t).zForce 4 i / ((q t).z 3 - (q t).z 4)) atTop (𝓝 0)) :
    Tendsto (fun t => (q t).delta 3 4 ^ 3) atTop (𝓝 ((mass 3 + mass 4)⁻¹)) := by
  have h3' := (((h3 0 (by decide)).const_mul (mass 0)).add
    ((h3 1 (by decide)).const_mul (mass 1))).add ((h3 2 (by decide)).const_mul (mass 2))
  have h4' := (((h4 0 (by decide)).const_mul (mass 0)).add
    ((h4 1 (by decide)).const_mul (mass 1))).add ((h4 2 (by decide)).const_mul (mass 2))
  have h := ((tendsto_const_nhds (x := (1 : ℂ))).sub (h3'.sub h4')).div_const (mass 3 + mass 4)
  norm_num at h
  convert h using 1
  funext t
  have hid := outer_z_difference (q t)
  have hz := (q t).z_separation_ne_zero (by decide : (3 : Fin 5) ≠ 4)
  field_simp [hP, hz]
  linear_combination -hid

theorem outer_cube_limit_of_order {eps : ℕ → ℂ}
    (heps : Tendsto eps atTop (𝓝 0))
    (hP : mass 3 + mass 4 ≠ 0)
    (hz : (fun t => (q t).z 3 - (q t).z 4) =Θ[atTop] eps)
    (h3 : ∀ i : Fin 5, i.val < 3 →
      (fun t => (q t).zForce 3 i) =O[atTop] (fun t => eps t ^ 2))
    (h4 : ∀ i : Fin 5, i.val < 3 →
      (fun t => (q t).zForce 4 i) =O[atTop] (fun t => eps t ^ 2)) :
    Tendsto (fun t => (q t).delta 3 4 ^ 3) atTop (𝓝 ((mass 3 + mass 4)⁻¹)) := by
  have hsmall : (fun t => eps t ^ 2) =o[atTop] eps := by
    have hh := (isLittleO_one_iff ℂ).2 heps
    convert hh.mul_isBigO (isBigO_refl eps atTop) using 1 <;> simp [pow_two, mul_comm]
  apply outer_cube_limit hP
  · intro i hi
    exact ((h3 i hi).trans_isLittleO (hsmall.trans_isBigO hz.2)).tendsto_div_nhds_zero
  · intro i hi
    exact ((h4 i hi).trans_isLittleO (hsmall.trans_isBigO hz.2)).tendsto_div_nhds_zero

/-- Sparse leading outer equations give the two attachment cubes from
the existing ScaledZWLimit, including all signed complex branches. -/
theorem attachment_cube_limits {s : ℕ → ℂ} (l : ScaledZWLimit q s)
    (hs : ∀ t, s t ≠ 0)
    (hm0 : mass 0 ≠ 0) (hm1 : mass 1 ≠ 0)
    (hM : mass 0 + mass 1 + mass 2 + mass 3 + mass 4 ≠ 0)
    (hin1 : l.w.position 1 = l.w.position 0)
    (hin2 : l.w.position 2 = l.w.position 0)
    (hout : l.w.position 4 = l.w.position 3)
    (hsep : l.w.position 3 ≠ l.w.position 0)
    (hf3 : ∀ j, j ≠ 0 → l.w.force 3 j = 0)
    (hf4 : ∀ j, j ≠ 1 → l.w.force 4 j = 0) :
    Tendsto (fun t => (q t).delta 0 3 ^ 3) atTop
      (𝓝 ((mass 0 + mass 1 + mass 2) /
        ((mass 0 + mass 1 + mass 2 + mass 3 + mass 4) * mass 0))) ∧
    Tendsto (fun t => (q t).delta 1 4 ^ 3) atTop
      (𝓝 ((mass 0 + mass 1 + mass 2) /
        ((mass 0 + mass 1 + mass 2 + mass 3 + mass 4) * mass 1))) := by
  have hcenter := l.w.component_balance Finset.univ (by simp)
  simp [Fin.sum_univ_succ, hin1, hin2, hout] at hcenter
  have he3 : l.w.position 3 = mass 0 * l.w.force 3 0 := by
    rw [l.w.balance 3, Finset.sum_eq_single 0]
    · intro b _ hb; rw [hf3 b hb, mul_zero]
    · simp
  have he4 : l.w.position 4 = mass 1 * l.w.force 4 1 := by
    rw [l.w.balance 4, Finset.sum_eq_single 1]
    · intro b _ hb; rw [hf4 b hb, mul_zero]
    · simp
  have hsep4 : l.w.position 4 ≠ l.w.position 1 := by simpa [hout, hin1] using hsep
  have h03 := l.delta_cube_limit_of_w_positions_ne hs 3 0 hsep
  have h14 := l.delta_cube_limit_of_w_positions_ne hs 4 1 hsep4
  constructor
  · convert h03 using 1
    · funext t; rw [(q t).delta_symm 0 3]
    · apply congrArg (fun z : ℂ => 𝓝 z)
      field_simp [hM, hm0, sub_ne_zero.mpr hsep]
      linear_combination (mass 0 + mass 1 + mass 2 + mass 3 + mass 4) * he3 - hcenter
  · convert h14 using 1
    · funext t; rw [(q t).delta_symm 1 4]
    · apply congrArg (fun z : ℂ => 𝓝 z)
      rw [hout, hin1]
      field_simp [hM, hm1, sub_ne_zero.mpr hsep]
      rw [hout] at he4
      linear_combination (mass 0 + mass 1 + mass 2 + mass 3 + mass 4) * he4 - hcenter

end CentralConfigurations.FiveBody.D9

