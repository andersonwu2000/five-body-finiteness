import CentralConfigurations.Asymptotics.DistanceProducts
import CentralConfigurations.Diagrams.InitialOrderLevels
import Mathlib.Data.Finset.Basic

/-!
# Lemma 4.2: the two distance-order tables

The source tables are on levels 1 through 5 (printed p.32, PDF p.37).
Index 0 is padded with empty entries. Every table entry is justified for
actual balanced singular sequences, retaining the polynomial distance branch.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

def edgeDistanceTable (z w : Fin 6) : Finset (Fin 6) :=
  match z.val, w.val with
  | 1, 5 | 5, 1 => {3}
  | 2, 4 | 4, 2 => {2}
  | 3, 3 => {1}
  | _, _ => ∅

def absentDistanceTable (z w : Fin 6) : Finset (Fin 6) :=
  match z.val, w.val with
  | 2, 4 | 3, 4 | 4, 2 | 4, 3 | 4, 4 => {2, 3, 4}
  | 2, 5 | 3, 5 | 4, 5 | 5, 2 | 5, 3 | 5, 4 => {4}
  | 5, 5 => {5}
  | _, _ => ∅

def distanceOrderTable (hasEdge : Bool) (z w : Fin 6) : Finset (Fin 6) :=
  if hasEdge then edgeDistanceTable z w else absentDistanceTable z w

theorem edgeDistanceTable_spec : ∀ z w r : Fin 6,
    r ∈ edgeDistanceTable z w ↔
      (z = 1 ∧ w = 5 ∧ r = 3) ∨ (z = 2 ∧ w = 4 ∧ r = 2) ∨
      (z = 3 ∧ w = 3 ∧ r = 1) ∨ (z = 4 ∧ w = 2 ∧ r = 2) ∨
      (z = 5 ∧ w = 1 ∧ r = 3) := by
  decide +kernel

theorem absentDistanceTable_spec : ∀ z w r : Fin 6,
    r ∈ absentDistanceTable z w ↔
      (z = 5 ∧ w = 5 ∧ r = 5) ∨
      (((z = 5 ∧ 2 ≤ w ∧ w ≤ 4) ∨ (w = 5 ∧ 2 ≤ z ∧ z ≤ 4)) ∧ r = 4) ∨
      (2 ≤ z ∧ z ≤ 4 ∧ 2 ≤ w ∧ w ≤ 4 ∧ (z = 4 ∨ w = 4) ∧ 2 ≤ r ∧ r ≤ 4) := by
  decide +kernel

theorem distanceOrderTable_symm : ∀ (e : Bool) (z w : Fin 6),
    distanceOrderTable e z w = distanceOrderTable e w z := by
  decide +kernel

theorem zero_not_mem_distanceOrderTable : ∀ (e : Bool) (z w : Fin 6),
    (0 : Fin 6) ∉ distanceOrderTable e z w := by
  decide +kernel

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem radius_one_iff_double (i j : Fin n) (hij : i ≠ j) :
    o.radius i j = 1 ↔ l.z.force i j ≠ 0 ∧ l.w.force i j ≠ 0 := by
  rw [(o.radius_level i j).one_iff_theta_lower]
  exact (ZWSystem.pairEstimateData q hb i j hij).double_force_iff_radius.symm.trans
    (and_congr (l.pair_z_stroke_iff hb i j hij) (l.pair_w_stroke_iff hb i j hij))

theorem radius_gt_one_of_absent_stroke (i j : Fin n) (hij : i ≠ j)
    (hab : l.z.force i j = 0 ∨ l.w.force i j = 0) : 1 < o.radius i j := by
  have hn : o.radius i j ≠ 1 := by
    intro hr
    have hd := (o.radius_one_iff_double l hb i j hij).mp hr
    rcases hab with hz | hw
    · exact hd.1 hz
    · exact hd.2 hw
  have h0 := o.radius_ne_zero hb i j hij
  omega

theorem z_stroke_radius_le_three (i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) : o.radius i j ≤ 3 :=
  (o.radius_level i j).le_three_iff_isBigO_middle.mpr
    ((ZWSystem.pairEstimateData q hb i j hij).stroke_radius_upper
      ((l.pair_z_stroke_iff hb i j hij).mpr hz))

theorem w_stroke_radius_le_three (i j : Fin n) (hij : i ≠ j)
    (hw : l.w.force i j ≠ 0) : o.radius i j ≤ 3 :=
  (o.radius_level i j).le_three_iff_isBigO_middle.mpr
    ((ZWSystem.pairEstimateData q hb i j hij).swap.stroke_radius_upper
      ((l.pair_w_stroke_iff hb i j hij).mpr hw))

theorem z_stroke_radius_three_iff (i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) : o.radius i j = 3 ↔ o.z i j = 5 := by
  rw [(o.radius_level i j).three_iff_theta_middle,
    (o.z_separation_level i j hij).five_iff_theta_upper]
  exact (ZWSystem.pairEstimateData q hb i j hij).stroke_radius_iff_z_maximal
    ((l.pair_z_stroke_iff hb i j hij).mpr hz)

theorem w_stroke_radius_three_iff (i j : Fin n) (hij : i ≠ j)
    (hw : l.w.force i j ≠ 0) : o.radius i j = 3 ↔ o.w i j = 5 := by
  rw [(o.radius_level i j).three_iff_theta_middle,
    (o.w_separation_level i j hij).five_iff_theta_upper]
  exact (ZWSystem.pairEstimateData q hb i j hij).swap.stroke_radius_iff_z_maximal
    ((l.pair_w_stroke_iff hb i j hij).mpr hw)

theorem radius_five_of_both_five (i j : Fin n) (hij : i ≠ j)
    (hz : o.z i j = 5) (hw : o.w i j = 5) : o.radius i j = 5 :=
  (o.radius_level i j).five_iff_theta_upper.mpr
    ((ZWSystem.pairEstimateData q hb i j hij).radius_theta_scale_of_both
      ((o.z_separation_level i j hij).five_iff_theta_upper.mp hz)
      ((o.w_separation_level i j hij).five_iff_theta_upper.mp hw))

theorem radius_ne_five_of_z_ne_five (i j : Fin n) (hij : i ≠ j)
    (hz : o.z i j ≠ 5) : o.radius i j ≠ 5 :=
  (o.radius_level i j).ne_five_iff_littleO_upper.mpr
    ((ZWSystem.pairEstimateData q hb i j hij).radius_littleO_scale_of_z
      ((o.z_separation_level i j hij).littleO_upper_of_ne_five hz))

theorem radius_ne_five_of_w_ne_five (i j : Fin n) (hij : i ≠ j)
    (hw : o.w i j ≠ 5) : o.radius i j ≠ 5 :=
  (o.radius_level i j).ne_five_iff_littleO_upper.mpr
    ((ZWSystem.pairEstimateData q hb i j hij).radius_littleO_scale_of_w
      ((o.w_separation_level i j hij).littleO_upper_of_ne_five hw))

theorem radius_gt_three_of_z_five (i j : Fin n) (hij : i ≠ j)
    (hz : o.z i j = 5) (hw : 1 < o.w i j) : 3 < o.radius i j :=
  (o.radius_level i j).three_lt_iff_middle_littleO.mpr
    ((ZWSystem.pairEstimateData q hb i j hij).swap.one_littleO_radius_of_z_large_w_maximal
      ((o.w_separation_level i j hij).lower_littleO_of_one_lt hw)
      ((o.z_separation_level i j hij).five_iff_theta_upper.mp hz))

theorem radius_gt_three_of_w_five (i j : Fin n) (hij : i ≠ j)
    (hw : o.w i j = 5) (hz : 1 < o.z i j) : 3 < o.radius i j :=
  (o.radius_level i j).three_lt_iff_middle_littleO.mpr
    ((ZWSystem.pairEstimateData q hb i j hij).one_littleO_radius_of_z_large_w_maximal
      ((o.z_separation_level i j hij).lower_littleO_of_one_lt hz)
      ((o.w_separation_level i j hij).five_iff_theta_upper.mp hw))

/-- Lemma 4.2, all five nonempty entries of D1. -/
theorem mem_edgeDistanceTable (i j : Fin n) (hij : i ≠ j)
    (he : l.z.force i j ≠ 0 ∨ l.w.force i j ≠ 0) :
    o.radius i j ∈ edgeDistanceTable (o.z i j) (o.w i j) := by
  apply (edgeDistanceTable_spec _ _ _).mpr
  have hs := o.edge_level_sum l hb i j hij he
  by_cases hz : l.z.force i j = 0
  · have hw := he.resolve_left (not_not.mpr hz)
    have hl := o.single_w_levels l hb i j hij hz hw
    have hr₁ := o.radius_gt_one_of_absent_stroke l hb i j hij (Or.inl hz)
    have hr₃ := o.w_stroke_radius_le_three l hb i j hij hw
    have heq := o.w_stroke_radius_three_iff l hb i j hij hw
    have hzw := o.w_stroke_five_iff_z_one l hb i j hij hw
    have hzb := (o.z i j).isLt
    have hwb := (o.w i j).isLt
    omega
  · by_cases hw : l.w.force i j = 0
    · have hl := o.single_z_levels l hb i j hij hz hw
      have hr₁ := o.radius_gt_one_of_absent_stroke l hb i j hij (Or.inr hw)
      have hr₃ := o.z_stroke_radius_le_three l hb i j hij hz
      have heq := o.z_stroke_radius_three_iff l hb i j hij hz
      have hzw := o.z_stroke_five_iff_w_one l hb i j hij hz
      have hzb := (o.z i j).isLt
      have hwb := (o.w i j).isLt
      omega
    · have hd := o.double_edge_levels l hb i j hij hz hw
      exact Or.inr (Or.inr (Or.inl ⟨hd.1, hd.2.1, hd.2.2⟩))

/-- Lemma 4.2, including every empty and nonempty entry of D2. -/
theorem mem_absentDistanceTable (i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j = 0) (hw : l.w.force i j = 0) :
    o.radius i j ∈ absentDistanceTable (o.z i j) (o.w i j) := by
  apply (absentDistanceTable_spec _ _ _).mpr
  have hl := o.absent_edge_levels l hb i j hij hz hw
  have hbig : 3 < o.z i j ∨ 3 < o.w i j := by
    by_contra! hn
    have hf := (ZWSystem.pairEstimateData q hb i j hij).small_separations_iff_double.mp
      ⟨(o.z_separation_level i j hij).le_three_iff_isBigO_middle.mp hn.1,
        (o.w_separation_level i j hij).le_three_iff_isBigO_middle.mp hn.2⟩
    exact ((l.pair_z_stroke_iff hb i j hij).mp hf.1) hz
  have hrlo := o.radius_gt_one_of_absent_stroke l hb i j hij (Or.inl hz)
  have hzb := (o.z i j).isLt
  have hwb := (o.w i j).isLt
  have hrb := (o.radius i j).isLt
  by_cases hz5 : o.z i j = 5
  · by_cases hw5 : o.w i j = 5
    · exact Or.inl ⟨hz5, hw5, o.radius_five_of_both_five hb i j hij hz5 hw5⟩
    · have hrlo' := o.radius_gt_three_of_z_five hb i j hij hz5 hl.2
      have hrhi := o.radius_ne_five_of_w_ne_five hb i j hij hw5
      apply Or.inr ∘ Or.inl
      exact ⟨Or.inl ⟨hz5, by omega, by omega⟩, by omega⟩
  · by_cases hw5 : o.w i j = 5
    · have hrlo' := o.radius_gt_three_of_w_five hb i j hij hw5 hl.1
      have hrhi := o.radius_ne_five_of_z_ne_five hb i j hij hz5
      apply Or.inr ∘ Or.inl
      exact ⟨Or.inr ⟨hw5, by omega, by omega⟩, by omega⟩
    · have hrhi := o.radius_ne_five_of_z_ne_five hb i j hij hz5
      apply Or.inr ∘ Or.inr
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

end SequenceOrderAssignment

end CentralConfigurations
