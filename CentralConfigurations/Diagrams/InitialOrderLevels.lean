import CentralConfigurations.Asymptotics.SequenceOrders

/-!
# Initial restrictions on actual order assignments

Proposition 4.4 and Lemma 4.1 are consequences of the previously proved
Estimates 1 and 2. All levels here belong to one actual balanced sequence,
not to a hypothetical solution of an integer constraint system.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))

theorem z_diagonal_five_iff (i : Fin n) : o.z i i = 5 ↔ l.z.position i ≠ 0 := by
  rw [(o.z_position_level i).five_iff_theta_upper]
  simpa only [ZWSystem.orderPositionScales, epsilonPositionScales, ZWSystem.epsilon_scale]
    using l.z_circle_order_iff i₀ j₀ hij₀ i

theorem w_diagonal_five_iff (i : Fin n) : o.w i i = 5 ↔ l.w.position i ≠ 0 := by
  rw [(o.w_position_level i).five_iff_theta_upper]
  simpa only [ZWSystem.orderPositionScales, epsilonPositionScales, ZWSystem.epsilon_scale]
    using l.w_circle_order_iff i₀ j₀ hij₀ i

theorem z_offDiagonal_five_iff (i j : Fin n) (hij : i ≠ j) :
    o.z i j = 5 ↔ l.z.position i ≠ l.z.position j := by
  rw [(o.z_separation_level i j hij).five_iff_theta_upper]
  simpa only [ZWSystem.orderPositionScales, epsilonPositionScales, ZWSystem.epsilon_scale]
    using l.z_separation_order_iff i₀ j₀ hij₀ i j

theorem w_offDiagonal_five_iff (i j : Fin n) (hij : i ≠ j) :
    o.w i j = 5 ↔ l.w.position i ≠ l.w.position j := by
  rw [(o.w_separation_level i j hij).five_iff_theta_upper]
  simpa only [ZWSystem.orderPositionScales, epsilonPositionScales, ZWSystem.epsilon_scale]
    using l.w_separation_order_iff i₀ j₀ hij₀ i j

variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

/-- Proposition 4.4(b), an exclusively z-colored edge. -/
theorem single_z_levels (i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j = 0) :
    3 < o.z i j ∧ 0 < o.w i j ∧ o.w i j < 3 := by
  have h := (ZWSystem.pairEstimateData q hb i j hij).single_z_separations
    ((l.pair_z_stroke_iff hb i j hij).mpr hz)
    ((l.pair_w_absent_iff hb i j hij).mpr hw)
  exact ⟨(o.z_separation_level i j hij).three_lt_iff_middle_littleO.mpr h.1,
    Fin.pos_iff_ne_zero.mpr (o.w_ne_zero hb i j hij),
    (o.w_separation_level i j hij).lt_three_iff_littleO_middle.mpr h.2⟩

/-- Proposition 4.4(b), an exclusively w-colored edge. -/
theorem single_w_levels (i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j = 0) (hw : l.w.force i j ≠ 0) :
    0 < o.z i j ∧ o.z i j < 3 ∧ 3 < o.w i j := by
  have h := (ZWSystem.pairEstimateData q hb i j hij).swap.single_z_separations
    ((l.pair_w_stroke_iff hb i j hij).mpr hw)
    ((l.pair_z_absent_iff hb i j hij).mpr hz)
  exact ⟨Fin.pos_iff_ne_zero.mpr (o.z_ne_zero hb i j hij),
    (o.z_separation_level i j hij).lt_three_iff_littleO_middle.mpr h.2,
    (o.w_separation_level i j hij).three_lt_iff_middle_littleO.mpr h.1⟩

/-- Proposition 4.4(b), a double edge. -/
theorem double_edge_levels (i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j ≠ 0) :
    o.z i j = 3 ∧ o.w i j = 3 ∧ o.radius i j = 1 := by
  let p := ZWSystem.pairEstimateData q hb i j hij
  have hz' := (l.pair_z_stroke_iff hb i j hij).mpr hz
  have hw' := (l.pair_w_stroke_iff hb i j hij).mpr hw
  have hr := p.double_force_iff_radius.mp ⟨hz', hw'⟩
  exact ⟨(o.z_separation_level i j hij).three_iff_theta_middle.mpr
      ((p.stroke_radius_iff_z_epsilon hz').mp hr),
    (o.w_separation_level i j hij).three_iff_theta_middle.mpr
      ((p.stroke_radius_iff_w_epsilon hz').mp hr),
    (o.radius_level i j).one_iff_theta_lower.mpr hr⟩

/-- Proposition 4.4(b), absence of both strokes excludes levels 0 and 1. -/
theorem absent_edge_levels (i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j = 0) (hw : l.w.force i j = 0) :
    1 < o.z i j ∧ 1 < o.w i j := by
  let p := ZWSystem.pairEstimateData q hb i j hij
  have hzn : o.z i j ≠ 1 := by
    intro hk
    have hs := (o.z_separation_level i j hij).one_iff_theta_lower.mp hk
    have hf := (p.swap.maximal_iff_w_small.mpr hs).1
    exact ((l.pair_w_stroke_iff hb i j hij).mp hf) hw
  have hwn : o.w i j ≠ 1 := by
    intro hk
    have hs := (o.w_separation_level i j hij).one_iff_theta_lower.mp hk
    have hf := (p.maximal_iff_w_small.mpr hs).1
    exact ((l.pair_z_stroke_iff hb i j hij).mp hf) hz
  have hz0 := o.z_ne_zero hb i j hij
  have hw0 := o.w_ne_zero hb i j hij
  constructor <;> omega

theorem z_stroke_five_iff_w_one (i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) : o.z i j = 5 ↔ o.w i j = 1 := by
  rw [(o.z_separation_level i j hij).five_iff_theta_upper,
    (o.w_separation_level i j hij).one_iff_theta_lower]
  exact (ZWSystem.pairEstimateData q hb i j hij).stroke_maximal_iff_w_small
    ((l.pair_z_stroke_iff hb i j hij).mpr hz)

theorem w_stroke_five_iff_z_one (i j : Fin n) (hij : i ≠ j)
    (hw : l.w.force i j ≠ 0) : o.w i j = 5 ↔ o.z i j = 1 := by
  rw [(o.w_separation_level i j hij).five_iff_theta_upper,
    (o.z_separation_level i j hij).one_iff_theta_lower]
  exact (ZWSystem.pairEstimateData q hb i j hij).swap.stroke_maximal_iff_w_small
    ((l.pair_w_stroke_iff hb i j hij).mpr hw)

/-- Lemma 4.1, the edge case. The sum is in the natural numbers, not Fin 6. -/
theorem edge_level_sum (i j : Fin n) (hij : i ≠ j)
    (he : l.z.force i j ≠ 0 ∨ l.w.force i j ≠ 0) :
    (o.z i j).val + (o.w i j).val = 6 := by
  by_cases hz : l.z.force i j = 0
  · have hw := he.resolve_left (not_not.mpr hz)
    have hl := o.single_w_levels l hb i j hij hz hw
    have hm := o.w_stroke_five_iff_z_one l hb i j hij hw
    have hzb := (o.z i j).isLt
    have hwb := (o.w i j).isLt
    omega
  · by_cases hw : l.w.force i j = 0
    · have hl := o.single_z_levels l hb i j hij hz hw
      have hm := o.z_stroke_five_iff_w_one l hb i j hij hz
      have hzb := (o.z i j).isLt
      have hwb := (o.w i j).isLt
      omega
    · have hl := o.double_edge_levels l hb i j hij hz hw
      simp only [hl.1, hl.2.1]
      decide

/-- Lemma 4.1, the case of no edge. -/
theorem absent_edge_level_sum (i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j = 0) (hw : l.w.force i j = 0) :
    6 ≤ (o.z i j).val + (o.w i j).val := by
  have hl := o.absent_edge_levels l hb i j hij hz hw
  by_contra hn
  have hzl : o.z i j ≤ 3 := by omega
  have hwl : o.w i j ≤ 3 := by omega
  have hs := (ZWSystem.pairEstimateData q hb i j hij).small_separations_iff_double.mp
    ⟨(o.z_separation_level i j hij).le_three_iff_isBigO_middle.mp hzl,
      (o.w_separation_level i j hij).le_three_iff_isBigO_middle.mp hwl⟩
  exact ((l.pair_z_stroke_iff hb i j hij).mp hs.1) hz

end SequenceOrderAssignment

end CentralConfigurations
