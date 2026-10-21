import CentralConfigurations.FiveBody.D6Butterfly.MetricOrders

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

theorem linear_pair_correction {f g a : ℕ → ℂ} {F G : ℂ}
    (hf : (fun t => f t-F) =O[atTop] a) (hg : (fun t => g t-G) =O[atTop] a) (x y : ℂ) :
    (fun t => x*f t+y*g t-(x*F+y*G)) =O[atTop] a :=
  ((hf.const_mul_left x).add (hg.const_mul_left y)).congr_left (fun t => by ring)

theorem first_translation {f a b c t : ℕ → ℂ} {F A B : ℂ}
    (hf : Tendsto f atTop (𝓝 F)) (ht : Tendsto t atTop (𝓝 0))
    (ha : (fun n => a n-A) =O[atTop] (fun n => t n^2))
    (hb : (fun n => b n-B) =O[atTop] (fun n => t n^2))
    (hc : c =O[atTop] (fun _ => (1:ℂ)))
    (he : ∀ n, f n=a n+t n*b n+t n^3*c n) :
    (fun n => f n-F-t n*B) =O[atTop] (fun n => t n^2) := by
  have htb := ht.isBigO_one ℂ
  have hbc : (fun n => t n*(b n-B)) =O[atTop] (fun n => t n^2) := by
    simpa only [one_mul] using htb.mul hb
  have htc := order_mul_bounded (isBigO_refl (fun n => t n^2) atTop) (bounded_mul htb hc)
  have hR : (fun n => f n-A-t n*B) =O[atTop] (fun n => t n^2) := by
    apply ((ha.add hbc).add htc).congr_left
    intro n
    rw [he n]
    ring
  have ht2 : Tendsto (fun n => t n^2) atTop (𝓝 0) := by simpa using ht.pow 2
  have hFA : F=A := sub_eq_zero.mp (tendsto_nhds_unique
    (by simpa using (hf.sub_const A).sub (ht.mul_const B)) (hR.trans_tendsto ht2))
  simpa only [hFA] using hR

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (g : ∀ t, PairGauge (q t))
  (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include l hm hd hb ha

theorem outer_translation_orders {u : Fin 6 → ℂ} {c : Fin 8 → ℂ} {h : Fin 4 → ℂ}
    (hu : ∀ e, Tendsto (fun t => (q t).delta (wingLeft e) (wingRight e)) atTop (𝓝 (u e)))
    (hun : ∀ e, u e≠0) (hc : ∀ i, Tendsto (fun t => (g t).coeff i) atTop (𝓝 (c i)))
    (hh : ∀ e, Tendsto (fun t => (g t).crossRoot e) atTop (𝓝 (h e))) :
    (fun t => (g t).coeff 6-c 6-(g t).time*(-(m 0:ℂ)*h 0^3+m 1*h 2^3)) =O[atTop] (fun t => (g t).time^2) ∧
    (fun t => (g t).coeff 7-c 7-(g t).time*(-(m 0:ℂ)*h 1^3+m 1*h 3^3)) =O[atTop] (fun t => (g t).time^2) ∧
    (fun t => (g t).coeff 2-c 2-(g t).time*(-(m 3:ℂ)*h 0^3+m 4*h 1^3)) =O[atTop] (fun t => (g t).time^2) ∧
    (fun t => (g t).coeff 3-c 3-(g t).time*(-(m 3:ℂ)*h 2^3+m 4*h 3^3)) =O[atTop] (fun t => (g t).time^2) := by
  have ht := time_zero l g (long_separations l hm hd).1 (long_separations l hm hd).2 ha
  have hδ := wing_cube_orders l hm hd g hb ha hu hun
  have hx (e : Fin 4) : (fun t => (g t).crossRoot e^3-h e^3) =O[atTop] (fun t => (g t).time^2) :=
    cube_difference_bigO (hh e) tendsto_const_nhds (cross_root_rigidity l hm hd g hb ha e (hh e)).2
  obtain ⟨hq1,hq2,hp3,hp4⟩ := short_difference_orders l hm hd g hb ha hu hun hc
  have hqq : (fun t => ((g t).coeff 6-(g t).coeff 7)-(c 6-c 7)) =O[atTop] (fun t => (g t).time^2) :=
    (hq1.sub hq2).congr_left (fun t => by ring)
  have hpp : (fun t => ((g t).coeff 2-(g t).coeff 3)-(c 2-c 3)) =O[atTop] (fun t => (g t).time^2) :=
    (hp3.sub hp4).congr_left (fun t => by ring)
  have C (i : Fin 8) := (hc i).isBigO_one ℂ
  have H (e : Fin 4) := ((hh e).pow 3).isBigO_one ℂ
  refine ⟨?_,?_,?_,?_⟩
  · apply first_translation (hc 6) ht
      (linear_pair_correction (product_correction (hδ 5) hqq (((hc 6).sub (hc 7)).isBigO_one ℂ))
        (product_correction (hδ 3) hq1 (((hc 6).sub (hc 5)).isBigO_one ℂ)) (m 4:ℂ) (m 2:ℂ))
      (linear_pair_correction (hx 0) (hx 2) (-(m 0:ℂ)) (m 1:ℂ))
      (bounded_mul ((C 6).sub (C 1)) (((H 0).const_mul_left (m 0:ℂ)).add ((H 2).const_mul_left (m 1:ℂ))))
    intro t
    dsimp [wingLeft,wingRight]
    simpa only [mul_assoc] using (g t).small_w3
  · have hqq' : (fun t => ((g t).coeff 7-(g t).coeff 6)-(c 7-c 6)) =O[atTop] (fun t => (g t).time^2) :=
      hqq.neg_left.congr_left (fun t => by ring)
    apply first_translation (hc 7) ht
      (linear_pair_correction (product_correction (hδ 5) hqq' (((hc 7).sub (hc 6)).isBigO_one ℂ))
        (product_correction (hδ 4) hq2 (((hc 7).sub (hc 5)).isBigO_one ℂ)) (m 3:ℂ) (m 2:ℂ))
      (linear_pair_correction (hx 1) (hx 3) (-(m 0:ℂ)) (m 1:ℂ))
      (bounded_mul ((C 7).sub (C 1)) (((H 1).const_mul_left (m 0:ℂ)).add ((H 3).const_mul_left (m 1:ℂ))))
    intro t
    dsimp [wingLeft,wingRight]
    simpa only [mul_assoc] using (g t).small_w4
  · apply first_translation (hc 2) ht
      (linear_pair_correction (product_correction (hδ 0) hpp (((hc 2).sub (hc 3)).isBigO_one ℂ))
        (product_correction (hδ 1) hp3 (((hc 2).sub (hc 4)).isBigO_one ℂ)) (m 1:ℂ) (m 2:ℂ))
      (linear_pair_correction (hx 0) (hx 1) (-(m 3:ℂ)) (m 4:ℂ))
      (bounded_mul ((C 2).sub (C 0)) (((H 0).const_mul_left (m 3:ℂ)).add ((H 1).const_mul_left (m 4:ℂ))))
    intro t
    dsimp [wingLeft,wingRight]
    simpa only [mul_assoc] using (g t).small_z0
  · have hpp' : (fun t => ((g t).coeff 3-(g t).coeff 2)-(c 3-c 2)) =O[atTop] (fun t => (g t).time^2) :=
      hpp.neg_left.congr_left (fun t => by ring)
    apply first_translation (hc 3) ht
      (linear_pair_correction (product_correction (hδ 0) hpp' (((hc 3).sub (hc 2)).isBigO_one ℂ))
        (product_correction (hδ 2) hp4 (((hc 3).sub (hc 4)).isBigO_one ℂ)) (m 0:ℂ) (m 2:ℂ))
      (linear_pair_correction (hx 2) (hx 3) (-(m 3:ℂ)) (m 4:ℂ))
      (bounded_mul ((C 3).sub (C 0)) (((H 2).const_mul_left (m 3:ℂ)).add ((H 3).const_mul_left (m 4:ℂ))))
    intro t
    dsimp [wingLeft,wingRight]
    simpa only [mul_assoc] using (g t).small_z1

end CentralConfigurations.FiveBody.D6

