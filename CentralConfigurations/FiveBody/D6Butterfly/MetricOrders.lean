import CentralConfigurations.FiveBody.D6Butterfly.ChartEquations

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

theorem product_correction {f g a : ℕ → ℂ} {F G : ℂ}
    (hf : (fun t => f t-F) =O[atTop] a)
    (hg : (fun t => g t-G) =O[atTop] a)
    (hgb : g =O[atTop] (fun _ => (1:ℂ))) :
    (fun t => f t*g t-F*G) =O[atTop] a :=
  ((order_mul_bounded hf hgb).add (hg.const_mul_left F)).congr_left (fun _ => by ring)

theorem signed_metric_correction {f d c t : ℕ → ℂ} {u D s : ℂ}
    (hu : u≠0) (hs : s≠0) (hf : Tendsto f atTop (𝓝 u)) (hd : Tendsto d atTop (𝓝 D))
    (ht : Tendsto t atTop (𝓝 0)) (hcb : c =O[atTop] (fun _ => (1:ℂ)))
    (horder : (fun n => f n^3-u^3) =O[atTop] (fun n => t n^2))
    (hmetric : ∀ n, (f n)⁻¹^2=s*d n+t n^2*c n*d n) :
    (fun n => d n-D) =O[atTop] (fun n => t n^2) := by
  have hδ := cube_root_difference_bigO hu hf horder
  have hi := inverse_difference_bigO hu hf hδ
  have hii := product_correction hi hi ((hf.inv₀ hu).isBigO_one ℂ)
  simp only [← pow_two] at hii
  have he := order_mul_bounded (isBigO_refl (fun n => t n^2) atTop) (bounded_mul hcb (hd.isBigO_one ℂ))
  have hS : (fun n => s*d n-u⁻¹^2) =O[atTop] (fun n => t n^2) := by
    apply (hii.sub he).congr_left
    intro n
    rw [hmetric n]
    ring
  have ht2 : Tendsto (fun n => t n^2) atTop (𝓝 0) := by simpa using ht.pow 2
  have hD : s*D=u⁻¹^2 := sub_eq_zero.mp (tendsto_nhds_unique
    ((hd.const_mul s).sub_const (u⁻¹^2)) (hS.trans_tendsto ht2))
  apply (hS.const_mul_left s⁻¹).congr_left
  intro n
  rw [← hD]
  field_simp [hs]

variable {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q)

theorem PairGauge.metric23 :
    (q.delta 2 3)⁻¹^2=(g.coeff 6-g.coeff 5)+g.time^2*(g.coeff 0-g.coeff 4)*(g.coeff 6-g.coeff 5) := by
  rw [inverse_metric g 2 3 (by decide)]
  obtain ⟨h3,-,-,-,-,-,h2,h5,h6,-⟩ := g.chart
  rw [h3,h2,h5,h6]
  field_simp [g.time_ne]
  ring

theorem PairGauge.metric24 :
    (q.delta 2 4)⁻¹^2= -(g.coeff 7-g.coeff 5)+g.time^2*(g.coeff 0-g.coeff 4)*(g.coeff 7-g.coeff 5) := by
  rw [inverse_metric g 2 4 (by decide)]
  obtain ⟨-,h4,-,-,-,-,h2,h5,-,h7⟩ := g.chart
  rw [h4,h2,h5,h7]
  field_simp [g.time_ne]
  ring

theorem PairGauge.metric02 :
    (q.delta 0 2)⁻¹^2=(g.coeff 2-g.coeff 4)+g.time^2*(g.coeff 1-g.coeff 5)*(g.coeff 2-g.coeff 4) := by
  rw [inverse_metric g 0 2 (by decide)]
  obtain ⟨-,-,h0,-,h2,-,h4,h5,-,-⟩ := g.chart
  rw [h0,h2,h4,h5]
  field_simp [g.time_ne]
  ring

theorem PairGauge.metric12 :
    (q.delta 1 2)⁻¹^2= -(g.coeff 3-g.coeff 4)+g.time^2*(g.coeff 1-g.coeff 5)*(g.coeff 3-g.coeff 4) := by
  rw [inverse_metric g 1 2 (by decide)]
  obtain ⟨-,-,-,h1,-,h3,h4,h5,-,-⟩ := g.chart
  rw [h1,h3,h4,h5]
  field_simp [g.time_ne]
  ring

variable {m : Fin 5 → ℝ} {qs : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit qs (fun t => (qs t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (gs : ∀ t, PairGauge (qs t))
  (hb : ∀ t, ‖(qs t).zVector‖=‖(qs t).wVector‖)
  (ha : Tendsto (fun t => (qs t).inverseScale) atTop (𝓝 0))
include l hm hd hb ha

theorem short_difference_orders {u : Fin 6 → ℂ} {c : Fin 8 → ℂ}
    (hu : ∀ e, Tendsto (fun t => (qs t).delta (wingLeft e) (wingRight e)) atTop (𝓝 (u e)))
    (hun : ∀ e, u e≠0) (hc : ∀ i, Tendsto (fun t => (gs t).coeff i) atTop (𝓝 (c i))) :
    (fun t => ((gs t).coeff 6-(gs t).coeff 5)-(c 6-c 5)) =O[atTop] (fun t => (gs t).time^2) ∧
    (fun t => ((gs t).coeff 7-(gs t).coeff 5)-(c 7-c 5)) =O[atTop] (fun t => (gs t).time^2) ∧
    (fun t => ((gs t).coeff 2-(gs t).coeff 4)-(c 2-c 4)) =O[atTop] (fun t => (gs t).time^2) ∧
    (fun t => ((gs t).coeff 3-(gs t).coeff 4)-(c 3-c 4)) =O[atTop] (fun t => (gs t).time^2) := by
  have ht := time_zero l gs (long_separations l hm hd).1 (long_separations l hm hd).2 ha
  have hδ := wing_cube_orders l hm hd gs hb ha hu hun
  have hP := ((hc 0).sub (hc 4)).isBigO_one ℂ
  have hQ := ((hc 1).sub (hc 5)).isBigO_one ℂ
  refine ⟨?_,?_,?_,?_⟩
  · apply signed_metric_correction (hun 3) (by norm_num : (1:ℂ)≠0) (hu 3) ((hc 6).sub (hc 5)) ht hP (hδ 3)
    intro t; simpa only [one_mul] using (gs t).metric23
  · apply signed_metric_correction (hun 4) (by norm_num : (-1:ℂ)≠0) (hu 4) ((hc 7).sub (hc 5)) ht hP (hδ 4)
    intro t; simpa only [neg_one_mul] using (gs t).metric24
  · apply signed_metric_correction (hun 1) (by norm_num : (1:ℂ)≠0) (hu 1) ((hc 2).sub (hc 4)) ht hQ (hδ 1)
    intro t; simpa only [one_mul] using (gs t).metric02
  · apply signed_metric_correction (hun 2) (by norm_num : (-1:ℂ)≠0) (hu 2) ((hc 3).sub (hc 4)) ht hQ (hδ 2)
    intro t; simpa only [neg_one_mul] using (gs t).metric12

end CentralConfigurations.FiveBody.D6
