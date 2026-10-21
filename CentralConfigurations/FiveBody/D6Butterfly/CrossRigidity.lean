import CentralConfigurations.FiveBody.D6Butterfly.LeadingMetric
import CentralConfigurations.Asymptotics.SequenceOrders

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology
noncomputable section

theorem cross_product_sign (e : Fin 4) :
    (leadingZ (crossLeft e)-leadingZ (crossRight e))*
      (leadingW (crossLeft e)-leadingW (crossRight e))=crossSign e := by
  fin_cases e
  · change (0-1)*(1-0:ℂ)= -1; norm_num
  · change (0-(-1))*(1-0:ℂ)=1; norm_num
  · change (0-1)*(-1-0:ℂ)=1; norm_num
  · change (0-(-1))*(-1-0:ℂ)= -1; norm_num

theorem cross_sign_sq (e : Fin 4) : (crossSign e)^2=1 := by
  fin_cases e <;> norm_num [crossSign]

def PairGauge.metricError {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) (e : Fin 4) : ℂ :=
  (g.time*g.normalized.z (crossLeft e)-g.time*g.normalized.z (crossRight e))*
    (g.time*g.normalized.w (crossLeft e)-g.time*g.normalized.w (crossRight e))-crossSign e

theorem PairGauge.metricError_eq {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) (e : Fin 4) :
    g.metricError e=g.time^2*((leadingZ (crossLeft e)-leadingZ (crossRight e))*
      (g.coeff (wCoeff (crossLeft e))-g.coeff (wCoeff (crossRight e)))+
      (leadingW (crossLeft e)-leadingW (crossRight e))*(g.coeff (zCoeff (crossLeft e))-g.coeff (zCoeff (crossRight e)))+
      g.time^2*(g.coeff (zCoeff (crossLeft e))-g.coeff (zCoeff (crossRight e)))*
        (g.coeff (wCoeff (crossLeft e))-g.coeff (wCoeff (crossRight e)))) := by
  dsimp [PairGauge.metricError]
  rw [g.scaled_z,g.scaled_z,g.scaled_w,g.scaled_w,← cross_product_sign e]
  ring

theorem PairGauge.cross_metric {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) (e : Fin 4) :
    (q.delta (crossLeft e) (crossRight e)/g.time)^2*(crossSign e+g.metricError e)=1 := by
  have hij : crossLeft e≠crossRight e := by fin_cases e <;> decide
  have hd := g.normalized.distance _ _ hij
  change q.delta (crossLeft e) (crossRight e)^2*((g.normalized.z (crossLeft e)-g.normalized.z (crossRight e))*
    (g.normalized.w (crossLeft e)-g.normalized.w (crossRight e)))=1 at hd
  dsimp [PairGauge.metricError]
  field_simp [g.time_ne]
  linear_combination g.time^2*hd

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (g : ∀ t, PairGauge (q t))
  (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include l hm hd hb ha

theorem metricError_bigO (e : Fin 4) :
    (fun t => (g t).metricError e) =O[atTop] (fun t => (g t).time^2) := by
  have hc i := bigO_one_of_bounded_range (coefficient_bounds l hm hd g hb ha i)
  have hz := (hc (zCoeff (crossLeft e))).sub (hc (zCoeff (crossRight e)))
  have hw := (hc (wCoeff (crossLeft e))).sub (hc (wCoeff (crossRight e)))
  have ht := time_zero l g (long_separations l hm hd).1 (long_separations l hm hd).2 ha
  have hlin := (hw.const_mul_left (leadingZ (crossLeft e)-leadingZ (crossRight e))).add
    (hz.const_mul_left (leadingW (crossLeft e)-leadingW (crossRight e)))
  have hquad : (fun t => (g t).time^2*((g t).coeff (zCoeff (crossLeft e))-(g t).coeff (zCoeff (crossRight e)))*
      ((g t).coeff (wCoeff (crossLeft e))-(g t).coeff (wCoeff (crossRight e)))) =O[atTop] (fun _ => (1:ℂ)) := by
    simpa only [one_mul] using (((ht.pow 2).isBigO_one ℂ).mul hz).mul hw
  have h := (isBigO_refl (fun t => (g t).time^2) atTop).mul (hlin.add hquad)
  simpa only [mul_one] using h.congr_left (fun t => (g t).metricError_eq e |>.symm)

theorem cross_root_rigidity (e : Fin 4) {u : ℂ}
    (hu : Tendsto (fun t => (q t).delta (crossLeft e) (crossRight e)/(g t).time) atTop (𝓝 u)) :
    u^2=crossSign e ∧
    (fun t => (q t).delta (crossLeft e) (crossRight e)/(g t).time-u) =O[atTop] (fun t => (g t).time^2) := by
  have hs := tendsto_nhds_unique (hu.pow 2) (cross_square_limit l hm hd g hb ha e)
  have hn : crossSign e≠0 := by intro h; have hh := cross_sign_sq e; simp [h] at hh
  have hun : u≠0 := by intro h; simp [h] at hs; exact hn hs.symm
  refine ⟨hs,inverse_square_metric_rigidity hun hn hu ?_
    (fun t => (g t).cross_metric e) (metricError_bigO l hm hd g hb ha e)⟩
  rw [hs,← pow_two]
  exact cross_sign_sq e

theorem exists_chart_with_cross_orders :
    ∃ c : Fin 8 → ℂ, ∃ u : Fin 6 → ℂ, ∃ h : Fin 4 → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ i, Tendsto (fun t => (g (φ t)).coeff i) atTop (𝓝 (c i))) ∧
      (∀ e, Tendsto (fun t => (q (φ t)).delta (wingLeft e) (wingRight e)) atTop (𝓝 (u e))) ∧
      (∀ e, u e≠0) ∧
      (∀ e, Tendsto (fun t => (q (φ t)).delta (crossLeft e) (crossRight e)/(g (φ t)).time) atTop (𝓝 (h e))) ∧
      (∀ e, h e^2=crossSign e) ∧
      (∀ e, (fun t => (q (φ t)).delta (crossLeft e) (crossRight e)/(g (φ t)).time-h e) =O[atTop]
        (fun t => (g (φ t)).time^2)) := by
  obtain ⟨c,u,h,φ,hφ,hc,hu,hun,hh⟩ := exists_chart_limits l hm hd g hb ha
  have hcros e := cross_root_rigidity (l.comp φ hφ.tendsto_atTop) hm hd (fun t => g (φ t))
    (fun t => hb (φ t)) (ha.comp hφ.tendsto_atTop) e (hh e)
  exact ⟨c,u,h,φ,hφ,hc,hu,hun,hh,(fun e => (hcros e).1),(fun e => (hcros e).2)⟩

end
end CentralConfigurations.FiveBody.D6
