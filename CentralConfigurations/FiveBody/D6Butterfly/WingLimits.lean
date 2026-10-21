import CentralConfigurations.FiveBody.D6Butterfly.Support
import CentralConfigurations.Asymptotics.ClusterPairLimits

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

def wingLeft : Fin 6 → Fin 5 := ![0,0,1,2,2,3]
def wingRight : Fin 6 → Fin 5 := ![1,2,2,3,4,4]
def crossLeft : Fin 4 → Fin 5 := ![0,0,1,1]
def crossRight : Fin 4 → Fin 5 := ![3,4,3,4]

theorem nonzero_cube_limit_of_w_stroke {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
    {a : ℕ → ℂ} (l : ScaledZWLimit q a) (hs : ∀ t, a t≠0) (i j : Fin 5)
    (hpos : l.w.position i≠l.w.position j) (hf : l.w.force i j≠0) :
    ∃ u : ℂ, u≠0 ∧ Tendsto (fun t => (q t).delta i j^3) atTop (𝓝 u) :=
  ⟨_,div_ne_zero hf (sub_ne_zero.mpr hpos),l.delta_cube_limit_of_w_positions_ne hs i j hpos⟩

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
include l hm hd

theorem wing_cube_limits (e : Fin 6) : ∃ u : ℂ, u≠0 ∧
    Tendsto (fun t => (q t).delta (wingLeft e) (wingRight e)^3) atTop (𝓝 u) := by
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
  obtain ⟨hz,hw⟩ := long_separations l hm hd
  have hz2 := l.z_position_zero_of_code hd 2 (by decide +kernel)
  have hw2 := l.w_position_zero_of_code hd 2 (by decide +kernel)
  fin_cases e
  · exact nonzero_cube_limit_of_w_stroke l hs 0 1 hw
      (l.w_force_ne_zero_of_code hd 0 1 (by decide) (by decide +kernel))
  · exact nonzero_cube_limit_of_w_stroke l hs 0 2 (by
      rw [hw2]; exact l.w_position_ne_zero_of_code hd 0 (by decide +kernel))
      (l.w_force_ne_zero_of_code hd 0 2 (by decide) (by decide +kernel))
  · exact nonzero_cube_limit_of_w_stroke l hs 1 2 (by
      rw [hw2]; exact l.w_position_ne_zero_of_code hd 1 (by decide +kernel))
      (l.w_force_ne_zero_of_code hd 1 2 (by decide) (by decide +kernel))
  · exact nonzero_cube_limit_of_w_stroke l.swap hs 2 3 (by
      change l.z.position 2≠l.z.position 3
      rw [hz2]; exact (l.z_position_ne_zero_of_code hd 3 (by decide +kernel)).symm)
      (l.z_force_ne_zero_of_code hd 2 3 (by decide) (by decide +kernel))
  · exact nonzero_cube_limit_of_w_stroke l.swap hs 2 4 (by
      change l.z.position 2≠l.z.position 4
      rw [hz2]; exact (l.z_position_ne_zero_of_code hd 4 (by decide +kernel)).symm)
      (l.z_force_ne_zero_of_code hd 2 4 (by decide) (by decide +kernel))
  · exact nonzero_cube_limit_of_w_stroke l.swap hs 3 4 hz
      (l.z_force_ne_zero_of_code hd 3 4 (by decide) (by decide +kernel))

theorem cross_delta_bigO (e : Fin 4) :
    (fun t => (q t).delta (crossLeft e) (crossRight e)) =O[atTop] (fun t => (q t).inverseScale) := by
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
  have hz : l.z.position (crossLeft e)≠l.z.position (crossRight e) := by
    have hi : l.z.position (crossLeft e)=0 := l.z_position_zero_of_code hd _ (by fin_cases e <;> decide +kernel)
    have hj : l.z.position (crossRight e)≠0 := l.z_position_ne_zero_of_code hd _ (by fin_cases e <;> decide +kernel)
    rw [hi]; exact hj.symm
  have hw : l.w.position (crossLeft e)≠l.w.position (crossRight e) := by
    have hi : l.w.position (crossLeft e)≠0 := l.w_position_ne_zero_of_code hd _ (by fin_cases e <;> decide +kernel)
    have hj : l.w.position (crossRight e)=0 := l.w_position_zero_of_code hd _ (by fin_cases e <;> decide +kernel)
    rw [hj]; exact hi
  have h := l.delta_div_scale_squared_limit hs _ _ hz hw
  apply IsBigO.of_pow (by decide : 2≠0)
  apply isBigO_of_div_tendsto_nhds
  · exact Eventually.of_forall (fun t ht => False.elim (pow_ne_zero 2 (hs t) ht))
  · simpa only [Pi.pow_apply,div_pow] using h

end CentralConfigurations.FiveBody.D6
