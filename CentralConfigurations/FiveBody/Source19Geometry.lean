import CentralConfigurations.Asymptotics.FiveBodyDisconnectedTorque
import CentralConfigurations.Enumeration.FiveBodySourceData
import CentralConfigurations.FourBody.DisconnectedPair

/-! Section 10.6: the central vertex is small in both coordinates.
The two outer positions in each color are distinct by positive mass
balance. Their isolated position classes and strokes pin the middle
vertex, supplying the bounds for the full five-body torque identity. -/

namespace CentralConfigurations
open Filter Asymptotics
open scoped Topology

theorem positive_pair_balance_distinct (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (u v : ℂ) (hu : u ≠ 0) (h : (a : ℂ)*u + (b : ℂ)*v = 0) : u ≠ v := by
  intro he
  have hn : (a : ℂ) + (b : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt (add_pos ha hb))
  apply mul_ne_zero hn hu
  rw [← he] at h
  linear_combination h

namespace ScaledZWLimit
variable {mass : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun a => (mass a : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ a, 0 < mass a) (hd : l.diagramCode = fiveBodySourceDiagram 18)
include hm hd

theorem five_body_source19_small_center_and_forces :
    (fun t => (q t).z 2) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).w 2) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).zForce 2 0) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).zForce 2 1) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).wForce 2 3) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).wForce 2 4) =O[atTop] (fun t => (q t).inverseScale) := by
  have hs := inverseScale_ne_zero (q := q) 0 1 (by decide)
  have hz0 := l.z_position_zero_of_code hd 0 (by decide +kernel)
  have hz1 := l.z_position_zero_of_code hd 1 (by decide +kernel)
  have hz2 := l.z_position_zero_of_code hd 2 (by decide +kernel)
  have hw2 := l.w_position_zero_of_code hd 2 (by decide +kernel)
  have hw3 := l.w_position_zero_of_code hd 3 (by decide +kernel)
  have hw4 := l.w_position_zero_of_code hd 4 (by decide +kernel)
  have hz3 := l.z_position_ne_zero_of_code hd 3 (by decide +kernel)
  have hz4 := l.z_position_ne_zero_of_code hd 4 (by decide +kernel)
  have hw0 := l.w_position_ne_zero_of_code hd 0 (by decide +kernel)
  have hw1 := l.w_position_ne_zero_of_code hd 1 (by decide +kernel)
  have hzb : (mass 3 : ℂ)*l.z.position 3 + mass 4*l.z.position 4 = 0 := by
    simpa [hz2] using l.z_component_balance_of_code hd {2,3,4} (by decide +kernel)
  have hwb : (mass 0 : ℂ)*l.w.position 0 + mass 1*l.w.position 1 = 0 := by
    simpa [hw2] using l.w_component_balance_of_code hd {0,1,2} (by decide +kernel)
  have hzne := positive_pair_balance_distinct _ _ (hm 3) (hm 4) _ _ hz3 hzb
  have hwne := positive_pair_balance_distinct _ _ (hm 0) (hm 1) _ _ hw0 hwb
  have hz0O := l.z_position_bigO_scale_of_isolated_w_position hs 0 (by
    intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact hwne
    · exact fun h => hw0 (h.trans hw2)
    · exact fun h => hw0 (h.trans hw3)
    · exact fun h => hw0 (h.trans hw4))
  have hz02 := l.z_separation_bigO_scale_of_maximal_w_pair hs 0 2 (by decide)
    (l.w_force_ne_zero_of_code hd 0 2 (by decide) (by decide +kernel))
    (fun h => hw0 (h.trans hw2))
  have hz2O := (hz0O.sub hz02).congr_left (fun t =>
    show (q t).z 0 - ((q t).z 0 - (q t).z 2) = (q t).z 2 by ring)
  have hw3O := l.swapAtScale.z_position_bigO_scale_of_isolated_w_position hs 3 (by
    intro j hj
    fin_cases j
    · exact fun h => hz3 (h.trans hz0)
    · exact fun h => hz3 (h.trans hz1)
    · exact fun h => hz3 (h.trans hz2)
    · exact (hj rfl).elim
    · exact hzne)
  have hw32 := l.swapAtScale.z_separation_bigO_scale_of_maximal_w_pair hs 3 2 (by decide)
    (l.z_force_ne_zero_of_code hd 3 2 (by decide) (by decide +kernel))
    (fun h => hz3 (h.trans hz2))
  have hw2O : (fun t => (q t).w 2) =O[atTop] (fun t => (q t).inverseScale) :=
    (hw3O.sub hw32).congr_left (fun t =>
      show (q t).w 3 - ((q t).w 3 - (q t).w 2) = (q t).w 2 by ring)
  refine ⟨hz2O,hw2O,?_,?_,?_,?_⟩
  · exact l.zForce_bigO_scale_of_distinct_w_positions hs 2 0 (fun h => hw0 (h.symm.trans hw2))
  · exact l.zForce_bigO_scale_of_distinct_w_positions hs 2 1 (fun h => hw1 (h.symm.trans hw2))
  · exact l.swapAtScale.zForce_bigO_scale_of_distinct_w_positions hs 2 3 (fun h => hz3 (h.symm.trans hz2))
  · exact l.swapAtScale.zForce_bigO_scale_of_distinct_w_positions hs 2 4 (fun h => hz4 (h.symm.trans hz2))

theorem five_body_source19_cross_torque_limit
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    Tendsto (fun t => fiveBodyCrossTorque (q t)/(q t).delta 3 0) atTop (𝓝 0) := by
  obtain ⟨hz,hw,hz0,hz1,hw3,hw4⟩ := l.five_body_source19_small_center_and_forces hm hd
  exact l.five_body_cross_torque_normalized_zero ha
    (five_body_cross_torque_bigO_square q _ hz hw hz0 hz1 hw3 hw4)

end ScaledZWLimit
end CentralConfigurations
