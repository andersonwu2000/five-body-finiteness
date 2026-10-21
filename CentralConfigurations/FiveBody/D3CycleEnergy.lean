import CentralConfigurations.FiveBody.D3CycleSupport
import CentralConfigurations.FiveBody.D3CycleMass

namespace CentralConfigurations.FiveBody.D3
open Filter Asymptotics
open scoped Topology BigOperators

def sideSum (m : Fin 5 → ℝ) (u : Fin 4 → ℂ) :=
  (m 1:ℂ)*m 2*u 0+(m 2:ℂ)*m 3*u 1+(m 3:ℂ)*m 4*u 2+(m 1:ℂ)*m 4*u 3

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 19)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include l hm hd ha

theorem complete_potential_limit {u : Fin 4 → ℂ} {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hu : ∀ e, Tendsto (fun t => (q (φ t)).delta (cycleLeft e) (cycleRight e)) atTop (𝓝 (u e))) :
    Tendsto (fun t => (q (φ t)).toNormalized.potential) atTop (𝓝 (sideSum m u)) := by
  have ho (e : Fin 6) := (off_cycle_zero l hm hd ha e).comp hφ.tendsto_atTop
  have h01 := (ho 0).const_mul ((m 0:ℂ)*m 1)
  have h02 := (ho 1).const_mul ((m 0:ℂ)*m 2)
  have h03 := (ho 2).const_mul ((m 0:ℂ)*m 3)
  have h04 := (ho 3).const_mul ((m 0:ℂ)*m 4)
  have h12 := (hu 0).const_mul ((m 1:ℂ)*m 2)
  have h13 := (ho 4).const_mul ((m 1:ℂ)*m 3)
  have h14 := (hu 3).const_mul ((m 1:ℂ)*m 4)
  have h23 := (hu 1).const_mul ((m 2:ℂ)*m 3)
  have h24 := (ho 5).const_mul ((m 2:ℂ)*m 4)
  have h34 := (hu 2).const_mul ((m 3:ℂ)*m 4)
  have h := ((((((((h01.add h02).add h03).add h04).add h12).add h13).add h14).add h23).add h24).add h34
  convert h using 1
  · ext t
    rw [NormalizedSystem.potential_eq_unordered]
    simp [NormalizedSystem.unorderedPotential,Fin.sum_univ_succ,ZWSystem.toNormalized,
      cycleLeft,cycleRight,offLeft,offRight]
    ring
  · congr 1
    dsimp [sideSum]
    ring

theorem actual_cycle_envelope {I0 : ℝ}
    (hI : ∀ t, (q t).toNormalized.potential=(I0:ℂ)) (hI0 : 0<I0) :
    ∃ x : Fin 4 → ℝ,
      (m 1+m 2)*(x 0)^3=1 ∧ (m 2+m 3)*(x 1)^3=1 ∧
      (m 3+m 4)*(x 2)^3=1 ∧ (m 1+m 4)*(x 3)^3=1 ∧ I0 ≤ cycleValue m x := by
  obtain ⟨u,φ,hφ,hu⟩ := exists_finite_coordinate_limits
    (fun t e => (q t).delta (cycleLeft e) (cycleRight e))
    (fun e => bounded_of_power_tendsto (by decide : 3≠0) (cycle_cubes l hm hd e))
  have hcube (e : Fin 4) : (u e)^3=(((m (cycleLeft e)+m (cycleRight e):ℝ):ℂ)⁻¹) :=
    tendsto_nhds_unique ((hu e).pow 3) ((cycle_cubes l hm hd e).comp hφ.tendsto_atTop)
  have hnorm (e : Fin 4) : (m (cycleLeft e)+m (cycleRight e))*‖u e‖^3=1 := by
    have h := congrArg norm (hcube e)
    simp only [norm_pow,norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_pos (add_pos (hm (cycleLeft e)) (hm (cycleRight e)))] at h
    rw [h]
    exact mul_inv_cancel₀ (ne_of_gt (add_pos (hm _) (hm _)))
  have he : (I0:ℂ)=sideSum m u := by
    have h := complete_potential_limit l hm hd ha hφ hu
    simp only [hI] at h
    exact tendsto_nhds_unique tendsto_const_nhds h
  refine ⟨(fun e => ‖u e‖),hnorm 0,hnorm 1,hnorm 2,hnorm 3,?_⟩
  have hn (i : Fin 5) : ‖(m i:ℂ)‖=m i := by simp [Complex.norm_real,abs_of_pos (hm i)]
  have hi : ‖(I0:ℂ)‖=I0 := by simp [Complex.norm_real,abs_of_pos hI0]
  rw [← hi,he]
  dsimp [sideSum,cycleValue]
  calc
    ‖(m 1:ℂ)*m 2*u 0+(m 2:ℂ)*m 3*u 1+(m 3:ℂ)*m 4*u 2+(m 1:ℂ)*m 4*u 3‖
      ≤ ‖(m 1:ℂ)*m 2*u 0‖+‖(m 2:ℂ)*m 3*u 1‖+‖(m 3:ℂ)*m 4*u 2‖+‖(m 1:ℂ)*m 4*u 3‖ := by
        have h1 := norm_add_le ((m 1:ℂ)*m 2*u 0) ((m 2:ℂ)*m 3*u 1)
        have h2 := norm_add_le ((m 1:ℂ)*m 2*u 0+(m 2:ℂ)*m 3*u 1) ((m 3:ℂ)*m 4*u 2)
        have h3 := norm_add_le ((m 1:ℂ)*m 2*u 0+(m 2:ℂ)*m 3*u 1+(m 3:ℂ)*m 4*u 2) ((m 1:ℂ)*m 4*u 3)
        linarith
    _ = _ := by simp only [norm_mul,hn]

/-- All four side phases and all six off-cycle potential terms are retained.
The only invariant hypothesis is the same exact physical scalar. -/
theorem false_of_chang20
    (_hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.potential=(I0:ℂ)) : False := by
  have hc := l.five_body_source20_mass_relation ha hd
  have hopp : m 1*m 3=m 2*m 4 := by exact_mod_cast hc
  obtain ⟨x,h0,h1,h2,h3,hbound⟩ := actual_cycle_envelope l hm hd ha hI hphysical.1
  exact energy_gap hm hopp hphysical x h0 h1 h2 h3 hbound

end CentralConfigurations.FiveBody.D3
