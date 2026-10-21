import CentralConfigurations.FiveBody.Source18Torque
import CentralConfigurations.Asymptotics.OneStrokeClusterLimits

/-! Actual pair and crossed metric limits for Chang source 18 (AK D2).
The canonical labels are triangle 0,1,2 and pair 3,4. -/

namespace CentralConfigurations.FiveBody.D2
open Filter Asymptotics
open scoped Topology BigOperators

variable {m : Fin 5 → ℝ}
  {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hd : l.diagramCode = fiveBodySourceDiagram 17)
include l hd

theorem pair_balances :
    l.z.position 3 = (m 4 : ℂ) * l.z.force 3 4 ∧
    l.z.position 4 = -((m 3 : ℂ) * l.z.force 3 4) := by
  have hcross (p i : Fin 5) (hp : p = 3 ∨ p = 4) (hi : i < 3) :
      l.z.force p i = 0 := by
    apply l.z_force_zero_of_code hd
    rcases hp with rfl | rfl <;> fin_cases i <;> simp_all
    all_goals decide +kernel
  constructor
  · have h := l.z.balance 3
    simpa [Fin.sum_univ_succ, l.z.diagonal, hcross 3 0 (by simp) (by decide),
      hcross 3 1 (by simp) (by decide), hcross 3 2 (by simp) (by decide)] using h
  · have h := l.z.balance 4
    simpa [Fin.sum_univ_succ, l.z.diagonal, l.z.antisymm 4 3,
      hcross 4 0 (by simp) (by decide), hcross 4 1 (by simp) (by decide),
      hcross 4 2 (by simp) (by decide)] using h

theorem pair_force_ne : l.z.force 3 4 ≠ 0 := by
  intro h
  have he := (pair_balances l hd).1
  simp only [h, mul_zero] at he
  exact l.z_position_ne_zero_of_code hd 3 (by decide +kernel) he

theorem pair_delta_cube_limit (hm : ∀ i, 0 < m i) :
    Tendsto (fun t => (q t).delta 3 4 ^ 3) atTop
      (𝓝 (((m 3 : ℂ) + m 4)⁻¹)) := by
  have hA : (m 3 : ℂ) + m 4 ≠ 0 := by
    exact_mod_cast ne_of_gt (add_pos (hm 3) (hm 4))
  have hdiff : l.z.position 3 - l.z.position 4 =
      ((m 3 : ℂ) + m 4) * l.z.force 3 4 := by
    rw [(pair_balances l hd).1, (pair_balances l hd).2]
    ring
  have hpos : l.z.position 3 ≠ l.z.position 4 := by
    apply sub_ne_zero.mp
    rw [hdiff]
    exact mul_ne_zero hA (pair_force_ne l hd)
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
  have h := l.swap.delta_cube_limit_of_w_positions_ne hs 3 4 hpos
  change Tendsto (fun t => (q t).delta 3 4 ^ 3) atTop
    (𝓝 (l.z.force 3 4 / (l.z.position 3 - l.z.position 4))) at h
  rw [hdiff] at h
  have he : l.z.force 3 4 / (((m 3 : ℂ) + m 4) * l.z.force 3 4) =
      ((m 3 : ℂ) + m 4)⁻¹ := by
    field_simp [hA, pair_force_ne l hd]
  rwa [he] at h

theorem cross_delta_zero (p : Fin 2) (i : Fin 3) :
    Tendsto (fun t => (q t).delta (Fin.natAdd 3 p) (i.castLE (by decide)))
      atTop (𝓝 0) := by
  have hP := l.z_position_ne_zero_of_code hd (Fin.natAdd 3 p) (by
    fin_cases p <;> decide +kernel)
  have hT := l.z_position_zero_of_code hd (i.castLE (by decide)) (by
    fin_cases i <;> decide +kernel)
  have hpos : l.z.position (Fin.natAdd 3 p) ≠
      l.z.position (i.castLE (by decide)) := by rwa [hT]
  have hforce := l.z_force_zero_of_code hd (Fin.natAdd 3 p) (i.castLE (by decide))
    (by fin_cases p <;> fin_cases i <;> decide +kernel)
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
  have h := l.swap.delta_cube_limit_of_w_positions_ne hs _ _ hpos
  apply tendsto_zero_of_complex_power (by decide : (3 : ℕ) ≠ 0)
  simpa only [ScaledZWLimit.swap, hforce, zero_div] using h

theorem cross_wForce_div_scale_zero
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (p : Fin 2) (i : Fin 3) :
    Tendsto (fun t => (q t).wForce (Fin.natAdd 3 p) (i.castLE (by decide)) /
      (q t).inverseScale) atTop (𝓝 0) := by
  have hzP := l.z_position_ne_zero_of_code hd (Fin.natAdd 3 p) (by
    fin_cases p <;> decide +kernel)
  have hzT := l.z_position_zero_of_code hd (i.castLE (by decide)) (by
    fin_cases i <;> decide +kernel)
  have hwP := l.w_position_zero_of_code hd (Fin.natAdd 3 p) (by
    fin_cases p <;> decide +kernel)
  have hwT := l.w_position_ne_zero_of_code hd (i.castLE (by decide)) (by
    fin_cases i <;> decide +kernel)
  exact l.swap.zForce_div_scale_zero_of_positions_ne
    (ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)) ha _ _
    (by change l.w.position _ ≠ l.w.position _; rw [hwP]; exact hwT.symm)
    (by change l.z.position _ ≠ l.z.position _; rw [hzT]; exact hzP)

end CentralConfigurations.FiveBody.D2
