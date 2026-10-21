import CentralConfigurations.FiveBody.SimpleMassRelations
import CentralConfigurations.FiveBody.D9Orders
import CentralConfigurations.Asymptotics.ClusterPairLimits

namespace CentralConfigurations.FiveBody.D3
open Filter Asymptotics
open scoped Topology

def cycleLeft : Fin 4 → Fin 5 := ![1,2,3,1]
def cycleRight : Fin 4 → Fin 5 := ![2,3,4,4]

def changToAK : Equiv.Perm (Fin 5) where
  toFun := ![1,2,3,4,0]
  invFun := ![4,0,1,2,3]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem chang20_to_akD3 : DiagramCode.transform (fiveBodySourceDiagram 19) changToAK true =
    (BinaryMatrixCode.fromMask 5 4713, BinaryMatrixCode.fromMask 5 5667) := by decide +kernel

theorem isolated_z_pair_cube {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
    {a : ℕ → ℂ} (l : ScaledZWLimit q a) (hs : ∀ t, a t≠0)
    (i j : Fin 5) (hpos : l.z.position i≠0) (_hmi : mass j≠0)
    (hpair : mass i+mass j≠0)
    (hi : l.z.position i=mass j*l.z.force i j)
    (hj : l.z.position j= -(mass i*l.z.force i j)) :
    Tendsto (fun t => (q t).delta i j^3) atTop (𝓝 (mass i+mass j)⁻¹) := by
  have hf : l.z.force i j≠0 := by intro h; rw [h,mul_zero] at hi; exact hpos hi
  have hdiff : l.z.position i-l.z.position j=(mass i+mass j)*l.z.force i j := by rw [hi,hj]; ring
  have hne : l.z.position i≠l.z.position j := by
    apply sub_ne_zero.mp; rw [hdiff]; exact mul_ne_zero hpair hf
  have h := l.swap.delta_cube_limit_of_w_positions_ne hs i j hne
  change Tendsto (fun t => (q t).delta i j^3) atTop
    (𝓝 (l.z.force i j/(l.z.position i-l.z.position j))) at h
  rw [hdiff] at h
  have he : l.z.force i j/((mass i+mass j)*l.z.force i j)=(mass i+mass j)⁻¹ := by field_simp [hpair,hf]
  rwa [he] at h

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 19)
include l hm hd

theorem cycle_cubes (e : Fin 4) :
    Tendsto (fun t => (q t).delta (cycleLeft e) (cycleRight e)^3) atTop
      (𝓝 (((m (cycleLeft e)+m (cycleRight e):ℝ):ℂ)⁻¹)) := by
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
  simp only [Complex.ofReal_add]
  have hsum (i j : Fin 5) : (m i : ℂ)+m j≠0 := by exact_mod_cast ne_of_gt (add_pos (hm i) (hm j))
  have hmass (i : Fin 5) : (m i : ℂ)≠0 := by exact_mod_cast ne_of_gt (hm i)
  fin_cases e
  · apply isolated_z_pair_cube l hs 1 2
      (l.z_position_ne_zero_of_code hd 1 (by decide +kernel)) (hmass 2) (hsum 1 2)
    · have h := l.z.balance 1
      simpa [Fin.sum_univ_succ,l.z.diagonal,
        l.z_force_zero_of_code hd 1 0 (by decide +kernel),
        l.z_force_zero_of_code hd 1 3 (by decide +kernel),
        l.z_force_zero_of_code hd 1 4 (by decide +kernel)] using h
    · have h := l.z.balance 2
      simpa [Fin.sum_univ_succ,l.z.diagonal,l.z.antisymm 2 1,
        l.z_force_zero_of_code hd 2 0 (by decide +kernel),
        l.z_force_zero_of_code hd 2 3 (by decide +kernel),
        l.z_force_zero_of_code hd 2 4 (by decide +kernel)] using h
  · apply isolated_z_pair_cube l.swap hs 2 3
      (l.w_position_ne_zero_of_code hd 2 (by decide +kernel)) (hmass 3) (hsum 2 3)
    · have h := l.w.balance 2
      simpa [ScaledZWLimit.swap,Fin.sum_univ_succ,l.w.diagonal,
        l.w_force_zero_of_code hd 2 0 (by decide +kernel),
        l.w_force_zero_of_code hd 2 1 (by decide +kernel),
        l.w_force_zero_of_code hd 2 4 (by decide +kernel)] using h
    · have h := l.w.balance 3
      simpa [ScaledZWLimit.swap,Fin.sum_univ_succ,l.w.diagonal,l.w.antisymm 3 2,
        l.w_force_zero_of_code hd 3 0 (by decide +kernel),
        l.w_force_zero_of_code hd 3 1 (by decide +kernel),
        l.w_force_zero_of_code hd 3 4 (by decide +kernel)] using h
  · apply isolated_z_pair_cube l hs 3 4
      (l.z_position_ne_zero_of_code hd 3 (by decide +kernel)) (hmass 4) (hsum 3 4)
    · have h := l.z.balance 3
      simpa [Fin.sum_univ_succ,l.z.diagonal,
        l.z_force_zero_of_code hd 3 0 (by decide +kernel),
        l.z_force_zero_of_code hd 3 1 (by decide +kernel),
        l.z_force_zero_of_code hd 3 2 (by decide +kernel)] using h
    · have h := l.z.balance 4
      simpa [Fin.sum_univ_succ,l.z.diagonal,l.z.antisymm 4 3,
        l.z_force_zero_of_code hd 4 0 (by decide +kernel),
        l.z_force_zero_of_code hd 4 1 (by decide +kernel),
        l.z_force_zero_of_code hd 4 2 (by decide +kernel)] using h
  · apply isolated_z_pair_cube l.swap hs 1 4
      (l.w_position_ne_zero_of_code hd 1 (by decide +kernel)) (hmass 4) (hsum 1 4)
    · have h := l.w.balance 1
      simpa [ScaledZWLimit.swap,Fin.sum_univ_succ,l.w.diagonal,
        l.w_force_zero_of_code hd 1 0 (by decide +kernel),
        l.w_force_zero_of_code hd 1 2 (by decide +kernel),
        l.w_force_zero_of_code hd 1 3 (by decide +kernel)] using h
    · have h := l.w.balance 4
      simpa [ScaledZWLimit.swap,Fin.sum_univ_succ,l.w.diagonal,l.w.antisymm 4 1,
        l.w_force_zero_of_code hd 4 0 (by decide +kernel),
        l.w_force_zero_of_code hd 4 2 (by decide +kernel),
        l.w_force_zero_of_code hd 4 3 (by decide +kernel)] using h

def offLeft : Fin 6 → Fin 5 := ![0,0,0,0,1,2]
def offRight : Fin 6 → Fin 5 := ![1,2,3,4,3,4]

theorem off_cycle_zero
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) (e : Fin 6) :
    Tendsto (fun t => (q t).delta (offLeft e) (offRight e)) atTop (𝓝 0) := by
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
  have hz0 := l.z_position_zero_of_code hd 0 (by decide +kernel)
  have hz1 := l.z_position_ne_zero_of_code hd 1 (by decide +kernel)
  have hz2 := l.z_position_ne_zero_of_code hd 2 (by decide +kernel)
  have hz3 := l.z_position_ne_zero_of_code hd 3 (by decide +kernel)
  have hz4 := l.z_position_ne_zero_of_code hd 4 (by decide +kernel)
  have h32 := l.z_position_eq_of_w_code_edge hd ha 3 2 (by decide) (by decide +kernel)
  have h41 := l.z_position_eq_of_w_code_edge hd ha 4 1 (by decide) (by decide +kernel)
  have h12 : l.z.position 1≠l.z.position 2 := by
    intro he
    have h := l.z_component_balance_of_code hd ({1,2}:Finset (Fin 5)) (by decide +kernel)
    simp only [Finset.sum_insert,Finset.sum_singleton,show (1:Fin 5) ∉ ({2}:Finset (Fin 5)) from by decide,
      not_false_eq_true,he] at h
    have hn : (m 1:ℂ)+m 2≠0 := by exact_mod_cast ne_of_gt (add_pos (hm 1) (hm 2))
    apply mul_ne_zero hn hz2
    linear_combination h
  have hne : l.z.position (offLeft e)≠l.z.position (offRight e) := by
    fin_cases e
    · exact fun h => hz1 (h.symm.trans hz0)
    · exact fun h => hz2 (h.symm.trans hz0)
    · exact fun h => hz3 (h.symm.trans hz0)
    · exact fun h => hz4 (h.symm.trans hz0)
    · simpa [offLeft,offRight,h32] using h12
    · simpa [offLeft,offRight,h41] using h12.symm
  have hf : l.z.force (offLeft e) (offRight e)=0 := by
    apply l.z_force_zero_of_code hd
    fin_cases e <;> decide +kernel
  have h := l.swap.delta_cube_limit_of_w_positions_ne hs (offLeft e) (offRight e) hne
  apply D9.zero_of_power (n := 3) (by decide)
  simpa only [ScaledZWLimit.swap,hf,zero_div] using h

end CentralConfigurations.FiveBody.D3
