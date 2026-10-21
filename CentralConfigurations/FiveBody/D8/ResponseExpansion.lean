import CentralConfigurations.FiveBody.D8.ChartForces
import CentralConfigurations.FiveBody.D8.AlgebraicTaylor

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology
noncomputable section

def responseSize {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) : ℂ := ↑(‖upperX q‖+‖upperY q‖)

theorem response_bounds {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass) :
    (fun t => upperX (q t)) =O[atTop] (fun t => responseSize (q t)) ∧
    (fun t => upperY (q t)) =O[atTop] (fun t => responseSize (q t)) := by
  constructor <;> apply isBigO_iff.mpr ⟨1,Filter.Eventually.of_forall ?_⟩ <;> intro t
  all_goals simp only [responseSize,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)),one_mul]
  · exact le_add_of_nonneg_right (norm_nonneg _)
  · exact le_add_of_nonneg_left (norm_nonneg _)

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
  {U : ℂ} (hUn : U≠0)
  (hU : Tendsto (fun t => (q t).delta 2 4/(q t).delta 2 3) atTop (𝓝 U))
  (hV : Tendsto (fun t => (q t).delta 3 4/(q t).delta 2 3) atTop (𝓝 U))
  (hshape : U^2*(m 2:ℂ)*m 3=((m 2:ℂ)+m 3)^2)
include l hm hd hUn hU hV hshape

theorem response_size_zero : Tendsto (fun t => responseSize (q t)) atTop (𝓝 0) := by
  have hx := (upper_x_zero l hm hd).norm
  have hy := (upper_y_zero l hm hd hUn hU hshape).norm
  simpa only [norm_zero,add_zero,Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto _).comp (hx.add hy)

theorem normalized_root_limits :
    Tendsto (fun t => rootFirst (q t) U) atTop (𝓝 1) ∧
    Tendsto (fun t => rootSecond (q t) U) atTop (𝓝 1) := by
  constructor
  · simpa only [rootFirst,div_div,div_self hUn] using hU.div_const U
  · simpa only [rootSecond,div_div,div_self hUn] using hV.div_const U

theorem row_expansions :
    (fun t => rowZ1 (q t) U-(upperX (q t)/2+3*(m 3:ℂ)/(2*m 2)*upperY (q t)))
      =O[atTop] (fun t => responseSize (q t)^2) ∧
    (fun t => rowZ2 (q t) U-(upperX (q t)/2+3*(m 2:ℂ)/(2*m 3)*upperY (q t)))
      =O[atTop] (fun t => responseSize (q t)^2) ∧
    (fun t => rowW1 (q t) U-((m 3:ℂ)-m 2)-(3*(m 2:ℂ)/(2*m 3)*upperX (q t)+upperY (q t)/2))
      =O[atTop] (fun t => responseSize (q t)^2) ∧
    (fun t => rowW2 (q t) U-((m 3:ℂ)-m 2)-(3*(m 3:ℂ)/(2*m 2)*upperX (q t)+upperY (q t)/2))
      =O[atTop] (fun t => responseSize (q t)^2) := by
  have hp : (m 2:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 2)
  have hq : (m 3:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 3)
  have hsz := response_size_zero l hm hd hUn hU hV hshape
  obtain ⟨hx,hy⟩ := response_bounds q
  obtain ⟨hf,hg⟩ := normalized_root_limits l hm hd hUn hU hV hshape
  have he t := normalized_root_metrics (q t) U (upper_mass_ne l hm hd) hp hq hUn hshape
  obtain ⟨hZ1,hW1⟩ := force_row_linearization hq hp hsz hx hy hf (fun t => (he t).1)
  obtain ⟨hZ2,hW2⟩ := force_row_linearization hp hq hsz hx.neg_left hy.neg_left hg (fun t => by
    simpa only [neg_div,← sub_eq_add_neg] using (he t).2)
  refine ⟨hZ1,?_,hW1,?_⟩
  · exact hZ2.neg_left.congr_left (fun t => by dsimp [rowZ2]; ring)
  · exact hW2.neg_left.congr_left (fun t => by dsimp [rowW2]; ring)

theorem weighted_difference_expansions :
    (fun t => (m 2:ℂ)*rowZ1 (q t) U+m 3*rowZ2 (q t) U-
      (((m 2:ℂ)+m 3)/2*(upperX (q t)+3*upperY (q t)))) =O[atTop] (fun t => responseSize (q t)^2) ∧
    (fun t => rowZ1 (q t) U-rowZ2 (q t) U-
      ((3/2:ℂ)*((m 3:ℂ)/m 2-(m 2:ℂ)/m 3)*upperY (q t))) =O[atTop] (fun t => responseSize (q t)^2) ∧
    (fun t => rowW1 (q t) U-rowW2 (q t) U-
      ((3/2:ℂ)*((m 2:ℂ)/m 3-(m 3:ℂ)/m 2)*upperX (q t))) =O[atTop] (fun t => responseSize (q t)^2) := by
  obtain ⟨h1,h2,h3,h4⟩ := row_expansions l hm hd hUn hU hV hshape
  have hp : (m 2:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 2)
  have hq : (m 3:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 3)
  refine ⟨?_,?_,?_⟩
  · apply ((h1.const_mul_left (m 2:ℂ)).add (h2.const_mul_left (m 3:ℂ))).congr_left
    intro t; field_simp [hp,hq]; ring
  · exact (h1.sub h2).congr_left (fun t => by ring)
  · exact (h3.sub h4).congr_left (fun t => by ring)

end
end CentralConfigurations.FiveBody.D8
