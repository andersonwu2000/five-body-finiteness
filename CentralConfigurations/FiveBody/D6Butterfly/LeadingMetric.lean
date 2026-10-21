import CentralConfigurations.FiveBody.D6Butterfly.Chart
import CentralConfigurations.FiveBody.D6Butterfly.RootOrders

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

theorem bigO_one_of_bounded_range {f : ℕ → ℂ} (h : Bornology.IsBounded (Set.range f)) :
    f =O[atTop] (fun _ => (1:ℂ)) := by
  obtain ⟨C,hC⟩ := isBounded_iff_forall_norm_le.mp h
  apply IsBigO.of_bound C
  exact Eventually.of_forall (fun t => by simpa using hC (f t) ⟨t,rfl⟩)

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (g : ∀ t, PairGauge (q t))
  (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include l hm hd hb ha

theorem quad_coeff_zero (i : Fin 8) :
    Tendsto (fun t => (g t).time^2*(g t).coeff i) atTop (𝓝 0) := by
  have ht := time_zero l g (long_separations l hm hd).1 (long_separations l hm hd).2 ha
  have hc := bigO_one_of_bounded_range (coefficient_bounds l hm hd g hb ha i)
  have hO : (fun t => (g t).time^2*(g t).coeff i) =O[atTop] (fun t => (g t).time^2) := by
    simpa only [mul_one] using (isBigO_refl (fun t => (g t).time^2) atTop).mul hc
  exact hO.trans_tendsto (by simpa using ht.pow 2)

theorem leading_positions :
    (∀ i, Tendsto (fun t => (g t).time*(g t).normalized.z i) atTop (𝓝 (leadingZ i))) ∧
    (∀ i, Tendsto (fun t => (g t).time*(g t).normalized.w i) atTop (𝓝 (leadingW i))) := by
  constructor
  · intro i
    have h := (quad_coeff_zero l hm hd g hb ha (zCoeff i)).const_add (leadingZ i)
    simpa only [add_zero] using h.congr (fun t => by
      rw [(g t).z_coordinates i]; field_simp [(g t).time_ne])
  · intro i
    have h := (quad_coeff_zero l hm hd g hb ha (wCoeff i)).const_add (leadingW i)
    simpa only [add_zero] using h.congr (fun t => by
      rw [(g t).w_coordinates i]; field_simp [(g t).time_ne])

def crossSign : Fin 4 → ℂ := ![-1,1,1,-1]

theorem cross_square_limit (e : Fin 4) :
    Tendsto (fun t => ((q t).delta (crossLeft e) (crossRight e)/(g t).time)^2)
      atTop (𝓝 (crossSign e)) := by
  obtain ⟨hz,hw⟩ := leading_positions l hm hd g hb ha
  have hn : (leadingZ (crossLeft e)-leadingZ (crossRight e))*
      (leadingW (crossLeft e)-leadingW (crossRight e))≠0 := by
    fin_cases e
    · change (0-1)*(1-0:ℂ)≠0; norm_num
    · change (0-(-1))*(1-0:ℂ)≠0; norm_num
    · change (0-1)*(-1-0:ℂ)≠0; norm_num
    · change (0-(-1))*(-1-0:ℂ)≠0; norm_num
  have h := (((hz (crossLeft e)).sub (hz (crossRight e))).mul
    ((hw (crossLeft e)).sub (hw (crossRight e)))).inv₀ hn
  have he (t) : (((g t).time*(g t).normalized.z (crossLeft e)-(g t).time*(g t).normalized.z (crossRight e))*
      ((g t).time*(g t).normalized.w (crossLeft e)-(g t).time*(g t).normalized.w (crossRight e)))⁻¹ =
      ((q t).delta (crossLeft e) (crossRight e)/(g t).time)^2 := by
    have hij : crossLeft e≠crossRight e := by fin_cases e <;> decide
    have hd := (g t).normalized.distance _ _ hij
    have hz := (g t).normalized.z_separation_ne_zero hij
    have hw := (g t).normalized.w_separation_ne_zero hij
    rw [← mul_sub,← mul_sub]
    field_simp [(g t).time_ne,hz,hw]
    change (q t).delta (crossLeft e) (crossRight e)^2 *
      (((g t).normalized.z (crossLeft e)-(g t).normalized.z (crossRight e))*
       ((g t).normalized.w (crossLeft e)-(g t).normalized.w (crossRight e)))=1 at hd
    linear_combination -hd
  have hsign : ((leadingZ (crossLeft e)-leadingZ (crossRight e))*
      (leadingW (crossLeft e)-leadingW (crossRight e)))⁻¹=crossSign e := by
    fin_cases e
    · change ((0-1)*(1-0:ℂ))⁻¹= -1; norm_num
    · change ((0-(-1))*(1-0:ℂ))⁻¹=1; norm_num
    · change ((0-1)*(-1-0:ℂ))⁻¹=1; norm_num
    · change ((0-(-1))*(-1-0:ℂ))⁻¹= -1; norm_num
  rw [hsign] at h
  exact h.congr he

end CentralConfigurations.FiveBody.D6
