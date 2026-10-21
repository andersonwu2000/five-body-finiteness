import CentralConfigurations.FiveBody.SecondaryMassRelations
import CentralConfigurations.FiveBody.Source19Geometry
import CentralConfigurations.FiveBody.OrdinaryDiagramIdentity
import CentralConfigurations.Asymptotics.SequenceOrders
import CentralConfigurations.Asymptotics.ClusterPairLimits

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology

def changToAK : Equiv.Perm (Fin 5) where
  toFun := ![2,3,0,1,4]
  invFun := ![2,3,0,1,4]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem chang7_to_akD8 : DiagramCode.transform (fiveBodySourceDiagram 6) changToAK false =
    (BinaryMatrixCode.fromMask 5 274,BinaryMatrixCode.fromMask 5 15872) := by decide +kernel

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
include l hm hd

theorem leading_positions :
    (∀ i, l.z.position i=0) ∧ l.w.position 2=0 ∧ l.w.position 3=0 ∧ l.w.position 4=0 ∧
    l.w.position 0≠0 ∧ l.w.position 1≠0 ∧ l.w.position 0≠l.w.position 1 := by
  have hz (i) : l.z.position i=0 := l.z_position_zero_of_code hd i (by fin_cases i <;> decide +kernel)
  have hw2 := l.w_position_zero_of_code hd 2 (by decide +kernel)
  have hw3 := l.w_position_zero_of_code hd 3 (by decide +kernel)
  have hw4 := l.w_position_zero_of_code hd 4 (by decide +kernel)
  have hw0 := l.w_position_ne_zero_of_code hd 0 (by decide +kernel)
  have hw1 := l.w_position_ne_zero_of_code hd 1 (by decide +kernel)
  have hbal : (m 0:ℂ)*l.w.position 0+m 1*l.w.position 1=0 := by
    simpa [hw4] using l.w_component_balance_of_code hd {0,1,4} (by decide +kernel)
  exact ⟨hz,hw2,hw3,hw4,hw0,hw1,positive_pair_balance_distinct _ _ (hm 0) (hm 1) _ _ hw0 hbal⟩

theorem lower_small_z :
    (fun t => (q t).z 0) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).z 1) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).z 4) =O[atTop] (fun t => (q t).inverseScale) := by
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
  obtain ⟨-,hw2,hw3,hw4,hw0,hw1,hw01⟩ := leading_positions l hm hd
  have hi0 : ∀ j : Fin 5, j≠0 → l.w.position 0≠l.w.position j := by
    intro j hj
    fin_cases j <;> simp_all
  have hi1 : ∀ j : Fin 5, j≠1 → l.w.position 1≠l.w.position j := by
    intro j hj
    fin_cases j
    · exact hw01.symm
    all_goals simp_all
  have hz0 := l.z_position_bigO_scale_of_isolated_w_position hs 0 hi0
  have hz1 := l.z_position_bigO_scale_of_isolated_w_position hs 1 hi1
  have hz40 := l.z_separation_bigO_scale_of_maximal_w_pair hs 4 0 (by decide)
    (l.w_force_ne_zero_of_code hd 4 0 (by decide) (by decide +kernel)) (by rw [hw4]; exact hw0.symm)
  exact ⟨hz0,hz1,(hz40.add hz0).congr_left (fun t => by ring)⟩

theorem upper_weighted_z :
    (fun t => (m 2:ℂ)*(q t).z 2+m 3*(q t).z 3) =O[atTop] (fun t => (q t).inverseScale) := by
  obtain ⟨hz0,hz1,hz4⟩ := lower_small_z l hm hd
  apply ((((hz0.const_mul_left (m 0:ℂ)).add (hz1.const_mul_left (m 1:ℂ))).add
    (hz4.const_mul_left (m 4:ℂ))).neg_left).congr_left
  intro t
  have hc := (q t).mass_center_z
  simp [Fin.sum_univ_succ] at hc
  linear_combination -hc

theorem inverseScale_small_upper :
    (fun t => (q t).inverseScale) =o[atTop] (fun t => (q t).z 2-(q t).z 3) :=
  l.scale_littleO_z_separation_of_equal_w_positions 2 3 (by decide)
    (by obtain ⟨-,hw2,hw3,-⟩ := leading_positions l hm hd; rw [hw2,hw3])

theorem epsilon_small_upper (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖) :
    (fun t => ((q t).epsilon:ℂ)) =o[atTop] (fun t => (q t).z 2-(q t).z 3) := by
  have h := (ZWSystem.pairEstimateData q hb 2 3 (by decide)).single_z_separations
    ((l.pair_z_stroke_iff hb 2 3 (by decide)).mpr (l.z_force_ne_zero_of_code hd 2 3 (by decide) (by decide +kernel)))
    ((l.pair_w_absent_iff hb 2 3 (by decide)).mpr (l.w_force_zero_of_code hd 2 3 (by decide +kernel)))
  exact h.1

theorem upper_scaled_zero :
    Tendsto (fun t => (q t).inverseScale*((q t).z 2-(q t).z 3)) atTop (𝓝 0) := by
  have hz := (leading_positions l hm hd).1
  simpa only [mul_sub,hz,sub_self] using (l.z_position 2).sub (l.z_position 3)

theorem lower_cube_limits :
    (∃ u : ℂ, u≠0 ∧ Tendsto (fun t => (q t).delta 0 1^3) atTop (𝓝 u)) ∧
    (∃ u : ℂ, u≠0 ∧ Tendsto (fun t => (q t).delta 0 4^3) atTop (𝓝 u)) ∧
    (∃ u : ℂ, u≠0 ∧ Tendsto (fun t => (q t).delta 1 4^3) atTop (𝓝 u)) := by
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
  obtain ⟨-,hw2,hw3,hw4,hw0,hw1,hw01⟩ := leading_positions l hm hd
  have hi (i j : Fin 5) (hpos : l.w.position i≠l.w.position j) (hf : l.w.force i j≠0) :
      ∃ u : ℂ, u≠0 ∧ Tendsto (fun t => (q t).delta i j^3) atTop (𝓝 u) :=
    ⟨_,div_ne_zero hf (sub_ne_zero.mpr hpos),l.delta_cube_limit_of_w_positions_ne hs i j hpos⟩
  exact ⟨hi 0 1 hw01 (l.w_force_ne_zero_of_code hd 0 1 (by decide) (by decide +kernel)),
    hi 0 4 (by rw [hw4]; exact hw0) (l.w_force_ne_zero_of_code hd 0 4 (by decide) (by decide +kernel)),
    hi 1 4 (by rw [hw4]; exact hw1) (l.w_force_ne_zero_of_code hd 1 4 (by decide) (by decide +kernel))⟩

end CentralConfigurations.FiveBody.D8
