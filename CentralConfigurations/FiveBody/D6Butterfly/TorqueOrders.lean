import CentralConfigurations.FiveBody.D6Butterfly.CommonOrders

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

theorem product_first_order {f g t : ℕ → ℂ} {F G D E : ℂ}
    (ht : Tendsto t atTop (𝓝 0)) (hgb : g =O[atTop] (fun _ => (1:ℂ)))
    (hf : (fun n => f n-F-t n*D) =O[atTop] (fun n => t n^2))
    (hg : (fun n => g n-G-t n*E) =O[atTop] (fun n => t n^2)) :
    (fun n => f n*g n-F*G-t n*(F*E+D*G)) =O[atTop] (fun n => t n^2) := by
  have haf : (fun n => F+t n*D) =O[atTop] (fun _ => (1:ℂ)) :=
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => F) atTop (𝓝 F)).add (ht.mul_const D)).isBigO_one ℂ
  have h := ((order_mul_bounded hf hgb).add (order_mul_bounded hg haf)).add
    ((isBigO_refl (fun n => t n^2) atTop).const_mul_left (D*E))
  exact h.congr_left (fun n => by ring)

theorem power_three_bigO_two {t : ℕ → ℂ} (ht : Tendsto t atTop (𝓝 0)) :
    (fun n => t n^3) =O[atTop] (fun n => t n^2) := by
  simpa only [pow_succ] using order_mul_bounded (isBigO_refl (fun n => t n^2) atTop) (ht.isBigO_one ℂ)

theorem first_coefficients_zero {f t : ℕ → ℂ} {A B : ℂ}
    (ht : Tendsto t atTop (𝓝 0)) (htn : ∀ n, t n≠0)
    (hf : f =O[atTop] (fun n => t n^3))
    (hjet : (fun n => f n-A-t n*B) =O[atTop] (fun n => t n^2)) : A=0 ∧ B=0 := by
  have ht2 : Tendsto (fun n => t n^2) atTop (𝓝 0) := by simpa using ht.pow 2
  have ht3 : Tendsto (fun n => t n^3) atTop (𝓝 0) := by simpa using ht.pow 3
  have hA : A=0 := by
    have he := tendsto_nhds_unique (((hf.trans_tendsto ht3).sub_const A).sub (ht.mul_const B)) (hjet.trans_tendsto ht2)
    simpa using (neg_eq_zero.mp (by simpa using he : -A=0))
  refine ⟨hA,coefficient_zero ht htn 1 ?_⟩
  apply ((hf.trans (power_three_bigO_two ht)).sub hjet).congr_left
  intro n
  rw [hA]
  ring

theorem torque_coefficient_order {v : ℕ → Fin 8 → ℂ} {c d : Fin 8 → ℂ} {t : ℕ → ℂ} (H K : ℂ)
    (hv : ∀ i, (fun n => v n i-c i-t n*d i) =O[atTop] (fun n => t n^2)) :
    (fun n => torqueCoefficient (v n) H K-torqueCoefficient c H K-t n*torqueCoefficient d H K) =O[atTop]
      (fun n => t n^2) := by
  have hq := ((hv 1).neg_left.add (((hv 6).add (hv 7)).const_mul_left (3/2:ℂ))).const_mul_left (H^3+K^3)
  have hp := ((hv 0).neg_left.add (((hv 2).add (hv 3)).const_mul_left (3/2:ℂ))).const_mul_left (H^3-K^3)
  exact (hq.add hp).congr_left (fun n => by dsimp [torqueCoefficient]; ring)

theorem order_times_cube_div_square {f t : ℕ → ℂ} (htn : ∀ n, t n≠0)
    (h : (fun n => t n^2*f n) =O[atTop] (fun n => t n^5)) :
    f =O[atTop] (fun n => t n^3) := by
  have hh := h.mul (isBigO_refl (fun n => (t n^2)⁻¹) atTop)
  apply hh.congr
  · intro n; field_simp [htn n]
  · intro n; field_simp [htn n]

noncomputable def reducedTorque {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) (H K : ℂ) : ℂ :=
  mass 2*(g.coeff 5*g.coeff 4-g.coeff 5*g.internalZ-g.coeff 4*g.internalW)-
    mass 3*mass 0*g.time*torqueCoefficient g.coeff H K

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (g : ∀ t, PairGauge (q t))
  (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include l hm hd hb ha

theorem reduced_torque_order {u : Fin 6 → ℂ} {c : Fin 8 → ℂ} {h : Fin 4 → ℂ}
    (hu : ∀ e, Tendsto (fun t => (q t).delta (wingLeft e) (wingRight e)) atTop (𝓝 (u e)))
    (hun : ∀ e, u e≠0) (hc : ∀ i, Tendsto (fun t => (g t).coeff i) atTop (𝓝 (c i)))
    (hh : ∀ e, Tendsto (fun t => (g t).crossRoot e) atTop (𝓝 (h e))) :
    (fun t => reducedTorque (g t) (h 0) (h 2)) =O[atTop] (fun t => (g t).time^3) := by
  apply order_times_cube_div_square (fun n => (g n).time_ne)
  apply (total_cross_torque_expansion l hm hd g hb ha hu hun hc hh).congr_left
  intro t
  rw [(g t).torque_identity]
  dsimp [reducedTorque]
  ring

end CentralConfigurations.FiveBody.D6
