import CentralConfigurations.FiveBody.D8.CrossScales
import CentralConfigurations.FiveBody.D8.ChartForces
import CentralConfigurations.Algebra.DisconnectedPairMass

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology
noncomputable section

def crossScale {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) := q.delta 2 0/upperS q

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
include l hm hd

theorem lower_balance : (m 0:ℂ)*l.w.position 0+m 1*l.w.position 1=0 := by
  simpa [(leading_positions l hm hd).2.2.2.1] using
    l.w_component_balance_of_code hd {0,1,4} (by decide +kernel)

theorem cross_ratio_squares :
    Tendsto (fun t => ((q t).delta 3 0/(q t).delta 2 0)^2) atTop (𝓝 (-(m 3:ℂ)/m 2)) ∧
    Tendsto (fun t => ((q t).delta 2 1/(q t).delta 2 0)^2) atTop (𝓝 (-(m 1:ℂ)/m 0)) ∧
    Tendsto (fun t => ((q t).delta 3 1/(q t).delta 2 0)^2) atTop
      (𝓝 ((m 3:ℂ)*m 1/((m 2:ℂ)*m 0))) := by
  have h20 := cross_delta_sq_scale l hm hd 2 0 (Or.inl rfl) (Or.inl rfl)
  have h20n := inv_ne_zero (mul_ne_zero (cross_coefficient_ne l hm hd 2 0 (Or.inl rfl) (Or.inl rfl)).1
    (neg_ne_zero.mpr (cross_coefficient_ne l hm hd 2 0 (Or.inl rfl) (Or.inl rfl)).2))
  have he (i j : Fin 5) (hi : i=2 ∨ i=3) (hj : j=0 ∨ j=1) :
      Tendsto (fun t => ((q t).delta i j/(q t).delta 2 0)^2) atTop
        (𝓝 ((upperZCoefficient m i*(-l.w.position j))⁻¹/(upperZCoefficient m 2*(-l.w.position 0))⁻¹)) := by
    apply ((cross_delta_sq_scale l hm hd i j hi hj).div h20 h20n).congr
    intro t
    change ((q t).delta i j^2/((q t).inverseScale/upperS (q t)))/
      ((q t).delta 2 0^2/((q t).inverseScale/upperS (q t)))=((q t).delta i j/(q t).delta 2 0)^2
    field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t,
      upperS_ne (q t) (upper_mass_ne l hm hd),(q t).delta_ne_zero 2 0 (by decide)]
  have hw0 := (leading_positions l hm hd).2.2.2.2.1
  have hw1 := (leading_positions l hm hd).2.2.2.2.2.1
  have hp : (m 2:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 2)
  have hq : (m 3:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 3)
  have ha : (m 0:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 0)
  have hbal := lower_balance l hm hd
  refine ⟨?_,?_,?_⟩
  · convert he 3 0 (Or.inr rfl) (Or.inl rfl) using 1
    dsimp [upperZCoefficient]; field_simp [hp,hq,hw0]
  · have hval : (upperZCoefficient m 2*(-l.w.position 1))⁻¹/(upperZCoefficient m 2*(-l.w.position 0))⁻¹= -(m 1:ℂ)/m 0 := by
      dsimp [upperZCoefficient]; field_simp [hq,ha,hw0,hw1]
      linear_combination hbal
    simpa only [hval] using he 2 1 (Or.inl rfl) (Or.inr rfl)
  · have hval : (upperZCoefficient m 3*(-l.w.position 1))⁻¹/(upperZCoefficient m 2*(-l.w.position 0))⁻¹= (m 3:ℂ)*m 1/((m 2:ℂ)*m 0) := by
      dsimp [upperZCoefficient]; field_simp [hp,hq,ha,hw0,hw1]
      linear_combination -hbal
    simpa only [hval] using he 3 1 (Or.inr rfl) (Or.inr rfl)

theorem w_force_cross_normalization (i j : Fin 5) (hij : i≠j) (t : ℕ) :
    (q t).wForce i j/crossScale (q t)=
      ((q t).delta i j/(q t).delta 2 0)/(((q t).z i-(q t).z j)/upperS (q t)) := by
  have hmij := (q t).distance i j hij
  dsimp [ZWSystem.wForce,crossScale]
  field_simp [(q t).delta_ne_zero 2 0 (by decide),upperS_ne (q t) (upper_mass_ne l hm hd),
    (q t).z_separation_ne_zero hij]
  linear_combination (q t).delta i j*hmij

/-- All sixteen crossed sheets are retained by square equations. -/
theorem mass_equalities_of_cross_difference
    (hcross : (fun t => crossW (q t) 2-crossW (q t) 3) =o[atTop] (fun t => crossScale (q t))) :
    m 2=m 3 ∧ m 0=m 1 := by
  obtain ⟨h30,h21,h31⟩ := cross_ratio_squares l hm hd
  let f : ℕ → Fin 3 → ℂ := fun t => ![(q t).delta 3 0/(q t).delta 2 0,
    (q t).delta 2 1/(q t).delta 2 0,(q t).delta 3 1/(q t).delta 2 0]
  have hB (i : Fin 3) : Bornology.IsBounded (Set.range (fun t => f t i)) := by
    fin_cases i
    · exact bounded_of_power_tendsto (by decide : 2≠0) h30
    · exact bounded_of_power_tendsto (by decide : 2≠0) h21
    · exact bounded_of_power_tendsto (by decide : 2≠0) h31
  obtain ⟨v,φ,hφ,hv⟩ := exists_finite_coordinate_limits f hB
  have hs0 : v 0^2= -(m 3:ℂ)/m 2 := tendsto_nhds_unique ((hv 0).pow 2) (h30.comp hφ.tendsto_atTop)
  have hs1 : v 1^2= -(m 1:ℂ)/m 0 := tendsto_nhds_unique ((hv 1).pow 2) (h21.comp hφ.tendsto_atTop)
  have hs2 : v 2^2= (m 3:ℂ)*m 1/((m 2:ℂ)*m 0) := tendsto_nhds_unique ((hv 2).pow 2) (h31.comp hφ.tendsto_atTop)
  have hp : (m 2:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 2)
  have hq : (m 3:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 3)
  have hnorm (i j : Fin 5) (hi : i=2 ∨ i=3) (hj : j=0 ∨ j=1) (V : ℂ)
      (hV : Tendsto (fun t => (q (φ t)).delta i j/(q (φ t)).delta 2 0) atTop (𝓝 V)) :
      Tendsto (fun t => (q (φ t)).wForce i j/crossScale (q (φ t))) atTop (𝓝 (V/upperZCoefficient m i)) := by
    have h := hV.div (((cross_coordinate_limits l hm hd i j hi hj).1).comp hφ.tendsto_atTop)
      (cross_coefficient_ne l hm hd i j hi hj).1
    apply h.congr
    intro t
    exact (w_force_cross_normalization l hm hd i j (by rcases hi with rfl|rfl <;> rcases hj with rfl|rfl <;> decide) (φ t)).symm
  have h20 : Tendsto (fun t => (q (φ t)).delta 2 0/(q (φ t)).delta 2 0) atTop (𝓝 1) := by
    simp only [div_self ((q (φ _)).delta_ne_zero 2 0 (by decide))]; exact tendsto_const_nhds
  have hsum := (((hnorm 2 0 (Or.inl rfl) (Or.inl rfl) 1 h20).const_mul (m 0:ℂ)).add
    ((hnorm 2 1 (Or.inl rfl) (Or.inr rfl) (v 1) (hv 1)).const_mul (m 1:ℂ))).sub
    (((hnorm 3 0 (Or.inr rfl) (Or.inl rfl) (v 0) (hv 0)).const_mul (m 0:ℂ)).add
    ((hnorm 3 1 (Or.inr rfl) (Or.inr rfl) (v 2) (hv 2)).const_mul (m 1:ℂ)))
  have hsum' := hsum.congr (show ∀ t, _=(crossW (q (φ t)) 2-crossW (q (φ t)) 3)/crossScale (q (φ t)) from
    fun t => by dsimp [crossW]; ring)
  have he := tendsto_nhds_unique hsum' (hcross.tendsto_div_nhds_zero.comp hφ.tendsto_atTop)
  have hforce : (m 0:ℂ)*m 2+(m 0:ℂ)*m 3*v 0+(m 1:ℂ)*m 2*v 1+(m 1:ℂ)*m 3*v 2=0 := by
    dsimp [upperZCoefficient] at he
    field_simp [hp,hq] at he
    linear_combination he
  apply disconnected_pair_mass_equalities (m 2) (m 3) (m 0) (m 1) (hm 2) (hm 3) (hm 0) (hm 1) (v 0) (v 1) (v 2)
  · simpa only [Complex.ofReal_neg,Complex.ofReal_div,neg_div] using hs0
  · simpa only [Complex.ofReal_neg,Complex.ofReal_div,neg_div] using hs1
  · simpa only [Complex.ofReal_mul,Complex.ofReal_div] using hs2
  · exact hforce

end
end CentralConfigurations.FiveBody.D8
