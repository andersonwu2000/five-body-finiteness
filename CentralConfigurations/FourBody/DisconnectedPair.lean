import CentralConfigurations.FourBody.SourceMassRelations
import CentralConfigurations.Algebra.DisconnectedPairMass
import CentralConfigurations.Asymptotics.DisconnectedPairLimits

/-!
# The actual disconnected diagram of Chang, Section 9.4

The component balances give three squared cross-distance ratio limits.
Common extraction and the exact subsystem torque give the wedge equation.
The positive-mass elimination concludes (9.4) on the original mass labels.
-/

namespace CentralConfigurations
noncomputable section
open Filter
open scoped Topology

theorem weighted_pair_balance_ratio {a b u v : ℂ} (ha : a ≠ 0) (hv : v ≠ 0)
    (h : a*u+b*v = 0) : u/v = -b/a := by
  field_simp [ha,hv]
  linear_combination h

theorem ScaledZWLimit.four_body_source4_mass_relation {mass : Fin 4 → ℝ}
    {q : ℕ → ZWSystem ℂ 4 (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ a, 0 < mass a)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (hd : l.diagramCode = fourBodySourceDiagram 3) :
    mass 0 = mass 1 ∧ mass 2 = mass 3 := by
  have hm0 (a : Fin 4) : (mass a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hm a)
  have hz0 := l.z_position_zero_of_code hd 0 (by decide +kernel)
  have hz1 := l.z_position_zero_of_code hd 1 (by decide +kernel)
  have hw2 := l.w_position_zero_of_code hd 2 (by decide +kernel)
  have hw3 := l.w_position_zero_of_code hd 3 (by decide +kernel)
  have hz2 := l.z_position_ne_zero_of_code hd 2 (by decide +kernel)
  have hz3 := l.z_position_ne_zero_of_code hd 3 (by decide +kernel)
  have hw0 := l.w_position_ne_zero_of_code hd 0 (by decide +kernel)
  have hw1 := l.w_position_ne_zero_of_code hd 1 (by decide +kernel)
  have hzb : (mass 2 : ℂ)*l.z.position 2 + mass 3*l.z.position 3 = 0 := by
    simpa using l.z_component_balance_of_code hd {2,3} (by decide +kernel)
  have hwb : (mass 0 : ℂ)*l.w.position 0 + mass 1*l.w.position 1 = 0 := by
    simpa using l.w_component_balance_of_code hd {0,1} (by decide +kernel)
  have hZ := weighted_pair_balance_ratio (hm0 2) hz3 hzb
  have hW := weighted_pair_balance_ratio (hm0 0) hw1 hwb
  have hα : Tendsto (fun t => ((q t).delta 2 1/(q t).delta 2 0)^2) atTop
      (𝓝 (((-(mass 1/mass 0) : ℝ)) : ℂ)) := by
    have h := l.delta_ratio_squared_limit hb 2 1 2 0 (by decide) (by decide)
      (by rwa [hz1]) (by simpa [hw2] using hw1.symm)
    simp only [hz0,hz1,hw2,sub_zero,zero_sub,neg_div_neg_eq,
      div_self hz2,one_mul,hW] at h
    simpa only [Complex.ofReal_neg,Complex.ofReal_div,neg_div] using h
  have hβ : Tendsto (fun t => ((q t).delta 3 0/(q t).delta 2 0)^2) atTop
      (𝓝 (((-(mass 3/mass 2) : ℝ)) : ℂ)) := by
    have h := l.delta_ratio_squared_limit hb 3 0 2 0 (by decide) (by decide)
      (by rwa [hz0]) (by simpa [hw3] using hw0.symm)
    simp only [hz0,hw2,hw3,sub_zero,zero_sub,neg_div_neg_eq,
      div_self hw0,mul_one,hZ] at h
    simpa only [Complex.ofReal_neg,Complex.ofReal_div,neg_div] using h
  have hγ : Tendsto (fun t => ((q t).delta 3 1/(q t).delta 2 0)^2) atTop
      (𝓝 (((mass 1*mass 3/(mass 0*mass 2) : ℝ)) : ℂ)) := by
    have h := l.delta_ratio_squared_limit hb 3 1 2 0 (by decide) (by decide)
      (by rwa [hz1]) (by simpa [hw3] using hw1.symm)
    simp only [hz0,hz1,hw2,hw3,sub_zero,zero_sub,neg_div_neg_eq,hZ,hW] at h
    convert h using 1
    congr 1
    push_cast
    simp only [div_eq_mul_inv,mul_inv]
    ring
  obtain ⟨α,β,γ,φ,hφ,hαlim,hβlim,hγlim,hαsq,hβsq,hγsq⟩ :=
    exists_simultaneous_three_square_limits hα hβ hγ
  have h20 := l.opposite_position_torque_limit 2 0 (by decide) hz2 hz0 hw2 hw0
  have h21 := l.opposite_position_torque_limit 2 1 (by decide) hz2 hz1 hw2 hw1
  have h30 := l.opposite_position_torque_limit 3 0 (by decide) hz3 hz0 hw3 hw0
  have h31 := l.opposite_position_torque_limit 3 1 (by decide) hz3 hz1 hw3 hw1
  have ht := four_body_cross_torque_root_relation (fun t => q (φ t)) α β γ
    hαlim hβlim hγlim
    (h20.comp hφ.tendsto_atTop) (h21.comp hφ.tendsto_atTop)
    (h30.comp hφ.tendsto_atTop) (h31.comp hφ.tendsto_atTop)
  exact disconnected_pair_mass_equalities _ _ _ _ (hm 0) (hm 1) (hm 2) (hm 3)
    α β γ hαsq hβsq hγsq ht

end
end CentralConfigurations
