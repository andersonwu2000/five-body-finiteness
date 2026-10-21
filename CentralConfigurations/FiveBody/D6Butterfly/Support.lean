import CentralConfigurations.FiveBody.D6Butterfly.Gauge

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

def changToAK : Equiv.Perm (Fin 5) where
  toFun := ![0,1,3,4,2]
  invFun := ![0,1,4,2,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem chang19_to_akD6 : DiagramCode.transform (fiveBodySourceDiagram 18) changToAK true =
    (BinaryMatrixCode.fromMask 5 307, BinaryMatrixCode.fromMask 5 15872) := by decide +kernel

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
include l hm hd

theorem long_separations : l.z.position 3≠l.z.position 4 ∧ l.w.position 0≠l.w.position 1 := by
  have hz2 := l.z_position_zero_of_code hd 2 (by decide +kernel)
  have hw2 := l.w_position_zero_of_code hd 2 (by decide +kernel)
  have hz3 := l.z_position_ne_zero_of_code hd 3 (by decide +kernel)
  have hw0 := l.w_position_ne_zero_of_code hd 0 (by decide +kernel)
  have hzb : (m 3:ℂ)*l.z.position 3+m 4*l.z.position 4=0 := by
    simpa [hz2] using l.z_component_balance_of_code hd {2,3,4} (by decide +kernel)
  have hwb : (m 0:ℂ)*l.w.position 0+m 1*l.w.position 1=0 := by
    simpa [hw2] using l.w_component_balance_of_code hd {0,1,2} (by decide +kernel)
  exact ⟨positive_pair_balance_distinct _ _ (hm 3) (hm 4) _ _ hz3 hzb,
    positive_pair_balance_distinct _ _ (hm 0) (hm 1) _ _ hw0 hwb⟩

theorem short_positions :
    (fun t => (q t).z 0) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).z 1) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).z 2) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).w 2) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).w 3) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).w 4) =O[atTop] (fun t => (q t).inverseScale) := by
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
  obtain ⟨hz2,hw2,-,-,-,-⟩ := l.five_body_source19_small_center_and_forces hm hd
  have hz : l.z.position 2=0 := l.z_position_zero_of_code hd 2 (by decide +kernel)
  have hw : l.w.position 2=0 := l.w_position_zero_of_code hd 2 (by decide +kernel)
  have h0 := l.z_separation_bigO_scale_of_maximal_w_pair hs 0 2 (by decide)
    (l.w_force_ne_zero_of_code hd 0 2 (by decide) (by decide +kernel))
    (by rw [hw]; exact l.w_position_ne_zero_of_code hd 0 (by decide +kernel))
  have h1 := l.z_separation_bigO_scale_of_maximal_w_pair hs 1 2 (by decide)
    (l.w_force_ne_zero_of_code hd 1 2 (by decide) (by decide +kernel))
    (by rw [hw]; exact l.w_position_ne_zero_of_code hd 1 (by decide +kernel))
  have h3 := l.swap.z_separation_bigO_scale_of_maximal_w_pair hs 3 2 (by decide)
    (l.z_force_ne_zero_of_code hd 3 2 (by decide) (by decide +kernel))
    (by change l.z.position 3≠l.z.position 2; rw [hz]; exact l.z_position_ne_zero_of_code hd 3 (by decide +kernel))
  have h4 := l.swap.z_separation_bigO_scale_of_maximal_w_pair hs 4 2 (by decide)
    (l.z_force_ne_zero_of_code hd 4 2 (by decide) (by decide +kernel))
    (by change l.z.position 4≠l.z.position 2; rw [hz]; exact l.z_position_ne_zero_of_code hd 4 (by decide +kernel))
  exact ⟨(h0.add hz2).congr_left (fun t => by ring),
    (h1.add hz2).congr_left (fun t => by ring),hz2,hw2,
    (h3.add hw2).congr_left (fun t => by dsimp [ZWSystem.swap]; ring),
    (h4.add hw2).congr_left (fun t => by dsimp [ZWSystem.swap]; ring)⟩

theorem pair_sums
    (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    (fun t => (q t).z 3+(q t).z 4) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).w 0+(q t).w 1) =O[atTop] (fun t => (q t).inverseScale) := by
  obtain ⟨hm01,hm34⟩ := l.five_body_source19_mass_relation hm hb ha hd
  obtain ⟨hz0,hz1,hz2,hw2,hw3,hw4⟩ := short_positions l hm hd
  have hn3 : (m 3:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 3)
  have hn0 : (m 0:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 0)
  constructor
  · have h := (((hz0.const_mul_left (m 0:ℂ)).add (hz1.const_mul_left (m 1:ℂ))).add
      (hz2.const_mul_left (m 2:ℂ))).const_mul_left (-(m 3:ℂ)⁻¹)
    apply h.congr_left
    intro t
    have hc := (q t).mass_center_z
    simp [Fin.sum_univ_succ,← hm34] at hc
    field_simp [hn3]
    linear_combination -hc
  · have h := (((hw2.const_mul_left (m 2:ℂ)).add (hw3.const_mul_left (m 3:ℂ))).add
      (hw4.const_mul_left (m 4:ℂ))).const_mul_left (-(m 0:ℂ)⁻¹)
    apply h.congr_left
    intro t
    have hc := (q t).mass_center_w
    simp [Fin.sum_univ_succ,← hm01] at hc
    field_simp [hn0]
    linear_combination -hc

end CentralConfigurations.FiveBody.D6
