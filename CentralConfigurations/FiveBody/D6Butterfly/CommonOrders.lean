import CentralConfigurations.FiveBody.D6Butterfly.TotalCrossTorque
import CentralConfigurations.FiveBody.D6Butterfly.StaticReciprocals

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology
noncomputable section

def driftD (b H K : ℂ) : ℂ := b*(K^3-H^3)
def driftE (a H K : ℂ) : ℂ := -a*(H^3+K^3)
def driftVector (a b d H K : ℂ) : Fin 8 → ℂ :=
  ![-(2*b+d)*driftE a H K/(2*a),-(2*a+d)*driftD b H K/(2*b),
    driftE a H K,driftE a H K,driftE a H K,driftD b H K,driftD b H K,driftD b H K]

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (g : ∀ t, PairGauge (q t))
  (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include l hm hd hb ha

theorem internal_force_orders {u : Fin 6 → ℂ} {c : Fin 8 → ℂ} {h : Fin 4 → ℂ}
    (hu : ∀ e, Tendsto (fun t => (q t).delta (wingLeft e) (wingRight e)) atTop (𝓝 (u e)))
    (hun : ∀ e, u e≠0) (hc : ∀ i, Tendsto (fun t => (g t).coeff i) atTop (𝓝 (c i)))
    (hh : ∀ e, Tendsto (fun t => (g t).crossRoot e) atTop (𝓝 (h e))) :
    (fun t => (g t).internalW-reciprocalZ u*c 5) =O[atTop] (fun t => (g t).time^2) ∧
    (fun t => (g t).internalZ-reciprocalW u*c 4) =O[atTop] (fun t => (g t).time^2) := by
  have hs := actual_wing_static l hm hd g hb ha hu hun hc hh
  obtain ⟨-,-,-,-,hA,hB⟩ := hs.reciprocal_data hun
  obtain ⟨hq1,hq2,hp3,hp4⟩ := short_difference_orders l hm hd g hb ha hu hun hc
  have hδ := wing_cube_orders l hm hd g hb ha hu hun
  have negD {i j : Fin 8} (h : (fun t => ((g t).coeff i-(g t).coeff j)-(c i-c j)) =O[atTop] (fun t => (g t).time^2)) :
      (fun t => ((g t).coeff j-(g t).coeff i)-(c j-c i)) =O[atTop] (fun t => (g t).time^2) :=
    h.neg_left.congr_left (fun t => by ring)
  obtain ⟨hm01,hm34⟩ := l.five_body_source19_mass_relation hm hb ha hd
  constructor
  · have hR := linear_pair_correction
      (product_correction (hδ 3) (negD hq1) (((hc 5).sub (hc 6)).isBigO_one ℂ))
      (product_correction (hδ 4) (negD hq2) (((hc 5).sub (hc 7)).isBigO_one ℂ)) (m 3:ℂ) (m 3:ℂ)
    apply hR.congr_left
    intro t
    dsimp [wingLeft,wingRight,PairGauge.internalW]
    rw [← hm34,← hA]
    ring
  · have hR := linear_pair_correction
      (product_correction (hδ 1) (negD hp3) (((hc 4).sub (hc 2)).isBigO_one ℂ))
      (product_correction (hδ 2) (negD hp4) (((hc 4).sub (hc 3)).isBigO_one ℂ)) (m 0:ℂ) (m 0:ℂ)
    apply hR.congr_left
    intro t
    dsimp [wingLeft,wingRight,PairGauge.internalZ]
    rw [← hm01,← hB]
    ring

theorem all_translation_orders {u : Fin 6 → ℂ} {c : Fin 8 → ℂ} {h : Fin 4 → ℂ}
    (hu : ∀ e, Tendsto (fun t => (q t).delta (wingLeft e) (wingRight e)) atTop (𝓝 (u e)))
    (hun : ∀ e, u e≠0) (hc : ∀ i, Tendsto (fun t => (g t).coeff i) atTop (𝓝 (c i)))
    (hh : ∀ e, Tendsto (fun t => (g t).crossRoot e) atTop (𝓝 (h e))) (i : Fin 8) :
    (fun t => (g t).coeff i-c i-(g t).time*driftVector (m 3) (m 0) (m 2) (h 0) (h 2) i) =O[atTop]
      (fun t => (g t).time^2) := by
  obtain ⟨h6,h7,h2,h3⟩ := outer_translation_orders l hm hd g hb ha hu hun hc hh
  obtain ⟨hs3,hs1⟩ := actual_cross_signs l hm hd g hb ha hu hun hc hh
  obtain ⟨hm01,hm34⟩ := l.five_body_source19_mass_relation hm hb ha hd
  have h6' : (fun t => (g t).coeff 6-c 6-(g t).time*driftD (m 0) (h 0) (h 2)) =O[atTop] (fun t => (g t).time^2) :=
    h6.congr_left (fun t => by rw [← hm01]; dsimp [driftD]; ring)
  have h7' : (fun t => (g t).coeff 7-c 7-(g t).time*driftD (m 0) (h 0) (h 2)) =O[atTop] (fun t => (g t).time^2) :=
    h7.congr_left (fun t => by rw [← hm01,hs3,hs1]; dsimp [driftD]; ring)
  have h2' : (fun t => (g t).coeff 2-c 2-(g t).time*driftE (m 3) (h 0) (h 2)) =O[atTop] (fun t => (g t).time^2) :=
    h2.congr_left (fun t => by rw [← hm34,hs1]; dsimp [driftE]; ring)
  have h3' : (fun t => (g t).coeff 3-c 3-(g t).time*driftE (m 3) (h 0) (h 2)) =O[atTop] (fun t => (g t).time^2) :=
    h3.congr_left (fun t => by rw [← hm34,hs3]; dsimp [driftE]; ring)
  obtain ⟨hq1,-,hp3,-⟩ := short_difference_orders l hm hd g hb ha hu hun hc
  have h5 : (fun t => (g t).coeff 5-c 5-(g t).time*driftD (m 0) (h 0) (h 2)) =O[atTop] (fun t => (g t).time^2) :=
    (h6'.sub hq1).congr_left (fun t => by ring)
  have h4 : (fun t => (g t).coeff 4-c 4-(g t).time*driftE (m 3) (h 0) (h 2)) =O[atTop] (fun t => (g t).time^2) :=
    (h2'.sub hp3).congr_left (fun t => by ring)
  have hs := actual_wing_static l hm hd g hb ha hu hun hc hh
  have hn0 : (m 0:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 0)
  have hn3 : (m 3:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 3)
  fin_cases i
  · have hh := ((((h2'.const_mul_left (m 0:ℂ)).add (h3'.const_mul_left (m 0:ℂ))).add
      (h4.const_mul_left (m 2:ℂ))).const_mul_left (-(2*(m 3:ℂ))⁻¹))
    apply hh.congr_left
    intro t
    have he := (g t).center_z
    simp only [← hm01,← hm34,sub_self,neg_zero,zero_div] at he
    change _=(g t).coeff 0-c 0-(g t).time*(-(2*(m 0:ℂ)+m 2)*driftE (m 3) (h 0) (h 2)/(2*m 3))
    field_simp [hn3]
    linear_combination -he+hs.center_z
  · have hh := ((((h5.const_mul_left (m 2:ℂ)).add (h6'.const_mul_left (m 3:ℂ))).add
      (h7'.const_mul_left (m 3:ℂ))).const_mul_left (-(2*(m 0:ℂ))⁻¹))
    apply hh.congr_left
    intro t
    have he := (g t).center_w
    simp only [← hm01,← hm34,sub_self,neg_zero,zero_div] at he
    change _=(g t).coeff 1-c 1-(g t).time*(-(2*(m 3:ℂ)+m 2)*driftD (m 0) (h 0) (h 2)/(2*m 0))
    field_simp [hn0]
    linear_combination -he+hs.center_w
  · exact h2'
  · exact h3'
  · exact h4
  · exact h5
  · exact h6'
  · exact h7'

end
end CentralConfigurations.FiveBody.D6
