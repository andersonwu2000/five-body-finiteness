import CentralConfigurations.FiveBody.D8.UpperChart
import CentralConfigurations.Asymptotics.FiniteLimitExtraction

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology

theorem delta_cube_ratio {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) (i j r s : Fin 5)
    (hij : i≠j) (hrs : r≠s) :
    (q.delta i j/q.delta r s)^3=(q.zForce i j/q.zForce r s)*((q.z r-q.z s)/(q.z i-q.z j)) := by
  dsimp [ZWSystem.zForce]
  field_simp [q.delta_ne_zero r s hrs,q.z_separation_ne_zero hrs,q.z_separation_ne_zero hij]

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
include l hm hd

theorem upper_force_ratio_limits :
    Tendsto (fun t => (q t).zForce 2 4/(q t).zForce 2 3) atTop (𝓝 (-(m 3:ℂ)/m 4)) ∧
    Tendsto (fun t => (q t).zForce 3 4/(q t).zForce 2 3) atTop (𝓝 ((m 2:ℂ)/m 4)) := by
  have hz := (leading_positions l hm hd).1
  have hn : (m 4:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 4)
  have hf := l.z_force_ne_zero_of_code hd 2 3 (by decide) (by decide +kernel)
  have hR := l.z.two_term_force_ratios 2 3 4 (by decide) (by decide) hn hf (hz 2) (hz 3)
    (fun r hr3 hr4 => l.z_force_zero_of_code hd 2 r (by fin_cases r <;> simp_all [fiveBodySourceDiagram] <;> decide +kernel))
    (fun r hr2 hr4 => l.z_force_zero_of_code hd 3 r (by fin_cases r <;> simp_all [fiveBodySourceDiagram] <;> decide +kernel))
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
  exact ⟨hR.1 ▸ tendsto_ratio_of_scaled hs hf (l.z_force 2 4) (l.z_force 2 3),
    hR.2 ▸ tendsto_ratio_of_scaled hs hf (l.z_force 3 4) (l.z_force 2 3)⟩

theorem upper_delta_ratio_cubes :
    Tendsto (fun t => ((q t).delta 2 4/(q t).delta 2 3)^3) atTop (𝓝 (-((m 2:ℂ)+m 3)/m 4)) ∧
    Tendsto (fun t => ((q t).delta 3 4/(q t).delta 2 3)^3) atTop (𝓝 (-((m 2:ℂ)+m 3)/m 4)) := by
  obtain ⟨hf2,hf3⟩ := upper_force_ratio_limits l hm hd
  obtain ⟨hz2,hz3⟩ := upper_z_ratio_limits l hm hd
  have hn2 : (m 2:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 2)
  have hn3 : (m 3:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 3)
  have hn4 : (m 4:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 4)
  have he (i : Fin 5) (hi : i≠4) (t : ℕ) :
      ((q t).zForce i 4/(q t).zForce 2 3)*(((m 2:ℂ)+m 3)/(((q t).z i-(q t).z 4)/upperS (q t)))=
        ((q t).delta i 4/(q t).delta 2 3)^3 := by
    rw [delta_cube_ratio (q t) i 4 2 3 hi (by decide)]
    dsimp [upperS]
    field_simp [upper_mass_ne l hm hd]
  constructor
  · have h := hf2.mul ((tendsto_const_nhds (x := (m 2:ℂ)+m 3)).div hz2 hn3)
    have hv : (-(m 3:ℂ)/m 4)*(((m 2:ℂ)+m 3)/m 3)= -((m 2:ℂ)+m 3)/m 4 := by field_simp [hn3,hn4]
    rw [hv] at h
    exact h.congr (he 2 (by decide))
  · have h := hf3.mul ((tendsto_const_nhds (x := (m 2:ℂ)+m 3)).div hz3 (neg_ne_zero.mpr hn2))
    have hv : ((m 2:ℂ)/m 4)*(((m 2:ℂ)+m 3)/(-(m 2:ℂ)))= -((m 2:ℂ)+m 3)/m 4 := by field_simp [hn2,hn4]
    rw [hv] at h
    exact h.congr (he 3 (by decide))

theorem exists_upper_root_limits : ∃ U V : ℂ, U≠0 ∧ V≠0 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
    Tendsto (fun t => (q (φ t)).delta 2 4/(q (φ t)).delta 2 3) atTop (𝓝 U) ∧
    Tendsto (fun t => (q (φ t)).delta 3 4/(q (φ t)).delta 2 3) atTop (𝓝 V) ∧
    U^3= -((m 2:ℂ)+m 3)/m 4 ∧ V^3= -((m 2:ℂ)+m 3)/m 4 := by
  obtain ⟨h2,h3⟩ := upper_delta_ratio_cubes l hm hd
  let f : ℕ → Fin 2 → ℂ := fun t => ![(q t).delta 2 4/(q t).delta 2 3,(q t).delta 3 4/(q t).delta 2 3]
  have hB (i : Fin 2) : Bornology.IsBounded (Set.range (fun t => f t i)) := by
    fin_cases i
    · exact bounded_of_power_tendsto (by decide : 3≠0) h2
    · exact bounded_of_power_tendsto (by decide : 3≠0) h3
  obtain ⟨v,φ,hφ,hv⟩ := exists_finite_coordinate_limits f hB
  have hc2 : v 0^3= -((m 2:ℂ)+m 3)/m 4 := tendsto_nhds_unique ((hv 0).pow 3) (h2.comp hφ.tendsto_atTop)
  have hc3 : v 1^3= -((m 2:ℂ)+m 3)/m 4 := tendsto_nhds_unique ((hv 1).pow 3) (h3.comp hφ.tendsto_atTop)
  have hn : -((m 2:ℂ)+m 3)/m 4≠0 := div_ne_zero (neg_ne_zero.mpr (upper_mass_ne l hm hd))
    (by exact_mod_cast ne_of_gt (hm 4))
  refine ⟨v 0,v 1,?_,?_,φ,hφ,hv 0,hv 1,hc2,hc3⟩
  · intro h; rw [h,zero_pow (by decide : 3≠0)] at hc2; exact hn hc2.symm
  · intro h; rw [h,zero_pow (by decide : 3≠0)] at hc3; exact hn hc3.symm

end CentralConfigurations.FiveBody.D8
