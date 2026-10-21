import CentralConfigurations.FiveBody.D8.CrossScales
import CentralConfigurations.FiveBody.D8.ResponseExpansion

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
  {U : ℂ} (hUn : U≠0) (hcu : (m 4:ℂ)*U^3= -((m 2:ℂ)+m 3))
include l hm hd

theorem crossZ_small (i : Fin 5) (hi : i=2 ∨ i=3) :
    (fun t => crossZ (q t) i) =o[atTop] (fun t => (q t).inverseScale) :=
  ((cross_zForce_small l hm hd i 0 hi (Or.inl rfl)).const_mul_left (m 0:ℂ)).add
    ((cross_zForce_small l hm hd i 1 hi (Or.inr rfl)).const_mul_left (m 1:ℂ))

theorem inverse_force_prefactor :
    (fun t => (((m 2:ℂ)+m 3)*(q t).delta 2 3^3*upperS (q t))⁻¹)
      =O[atTop] (fun t => (q t).inverseScale) := by
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
  have hn := l.z_force_ne_zero_of_code hd 2 3 (by decide) (by decide +kernel)
  have he : Tendsto (fun t => (((m 2:ℂ)+m 3)*(q t).delta 2 3^3*upperS (q t))⁻¹/(q t).inverseScale)
      atTop (𝓝 (l.z.force 2 3)⁻¹) := by
    have h := (l.z_force 2 3).inv₀ hn
    apply h.congr
    intro t
    dsimp [upperS,ZWSystem.zForce]
    field_simp [hs t,upper_mass_ne l hm hd]
  exact isBigO_of_div_tendsto_nhds (Filter.Eventually.of_forall (fun t he => False.elim (hs t he))) _ he

include hUn hcu

theorem row_z_orders :
    (fun t => rowZ1 (q t) U) =O[atTop] (fun t => (q t).inverseScale*upperS (q t)) ∧
    (fun t => rowZ2 (q t) U) =O[atTop] (fun t => (q t).inverseScale*upperS (q t)) := by
  have hs := isBigO_refl (fun t => upperS (q t)) atTop
  have hz2 : (fun t => (q t).z 2) =O[atTop] (fun t => upperS (q t)) :=
    isBigO_of_div_tendsto_nhds (Filter.Eventually.of_forall (fun t he => False.elim (upperS_ne (q t) (upper_mass_ne l hm hd) he))) _
      (upper_z_absolute_ratio l hm hd 2 (Or.inl rfl))
  have hz3 : (fun t => (q t).z 3) =O[atTop] (fun t => upperS (q t)) :=
    isBigO_of_div_tendsto_nhds (Filter.Eventually.of_forall (fun t he => False.elim (upperS_ne (q t) (upper_mass_ne l hm hd) he))) _
      (upper_z_absolute_ratio l hm hd 3 (Or.inr rfl))
  have hc2 := (crossZ_small l hm hd 2 (Or.inl rfl)).isBigO.trans (inverseScale_small_s l hm hd).isBigO
  have hc3 := (crossZ_small l hm hd 3 (Or.inr rfl)).isBigO.trans (inverseScale_small_s l hm hd).isBigO
  have hfn t : ((m 2:ℂ)+m 3)*(q t).delta 2 3^3*upperS (q t)≠0 := mul_ne_zero
    (mul_ne_zero (upper_mass_ne l hm hd) (pow_ne_zero 3 ((q t).delta_ne_zero 2 3 (by decide))))
    (upperS_ne (q t) (upper_mass_ne l hm hd))
  constructor
  · refine ((inverse_force_prefactor l hm hd).mul (hz2.sub hc2)).congr_left ?_
    intro t
    rw [(upper_force_equations (q t) U (upper_mass_ne l hm hd) hUn hcu).1]
    simp only [add_sub_cancel_right,inv_mul_cancel_left₀ (hfn t)]
  · refine ((inverse_force_prefactor l hm hd).mul (hz3.sub hc3)).congr_left ?_
    intro t
    rw [(upper_force_equations (q t) U (upper_mass_ne l hm hd) hUn hcu).2.1]
    simp only [add_sub_cancel_right,inv_mul_cancel_left₀ (hfn t)]

theorem weighted_row_z_order :
    (fun t => (m 2:ℂ)*rowZ1 (q t) U+m 3*rowZ2 (q t) U)
      =O[atTop] (fun t => (q t).inverseScale^2) := by
  have hc := ((crossZ_small l hm hd 2 (Or.inl rfl)).const_mul_left (m 2:ℂ)).add
    ((crossZ_small l hm hd 3 (Or.inr rfl)).const_mul_left (m 3:ℂ))
  have he := (inverse_force_prefactor l hm hd).mul ((upper_weighted_z l hm hd).sub hc.isBigO)
  apply he.congr
  · intro t
    have hE := upper_force_equations (q t) U (upper_mass_ne l hm hd) hUn hcu
    rw [hE.1,hE.2.1]
    field_simp [upper_mass_ne l hm hd,(q t).delta_ne_zero 2 3 (by decide),upperS_ne (q t) (upper_mass_ne l hm hd)]
    ring
  · intro t; ring

theorem difference_row_z_asymptotic :
    (fun t => rowZ1 (q t) U-rowZ2 (q t) U-((q t).delta 2 3)⁻¹^3)
      =o[atTop] (fun t => (q t).inverseScale*upperS (q t)) := by
  have hc := ((crossZ_small l hm hd 2 (Or.inl rfl)).sub (crossZ_small l hm hd 3 (Or.inr rfl))).trans
    (inverseScale_small_s l hm hd)
  have he := ((inverse_force_prefactor l hm hd).mul_isLittleO hc).neg_left
  apply he.congr_left
  intro t
  have hE := upper_force_equations (q t) U (upper_mass_ne l hm hd) hUn hcu
  have hdif : (q t).z 2-(q t).z 3=((m 2:ℂ)+m 3)*upperS (q t) := by
    dsimp [upperS]; field_simp [upper_mass_ne l hm hd]
  field_simp [upper_mass_ne l hm hd,(q t).delta_ne_zero 2 3 (by decide),upperS_ne (q t) (upper_mass_ne l hm hd)]
  linear_combination hE.1-hE.2.1-hdif

end CentralConfigurations.FiveBody.D8
