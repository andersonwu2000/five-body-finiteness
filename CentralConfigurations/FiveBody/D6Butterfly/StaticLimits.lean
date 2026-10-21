import CentralConfigurations.FiveBody.D6Butterfly.Translations
import CentralConfigurations.FiveBody.D6Butterfly.WingCatalogue

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

theorem small_equation_limit {f a b c t : ℕ → ℂ} {F A : ℂ}
    (hf : Tendsto f atTop (𝓝 F)) (ha : Tendsto a atTop (𝓝 A)) (ht : Tendsto t atTop (𝓝 0))
    (hb : b =O[atTop] (fun _ => (1:ℂ))) (hc : c =O[atTop] (fun _ => (1:ℂ)))
    (he : ∀ n, f n=a n+t n*b n+t n^3*c n) : F=A := by
  have h : (fun n => f n-a n) =O[atTop] t := by
    apply (order_mul_bounded (isBigO_refl t atTop) (hb.add (bounded_mul ((ht.pow 2).isBigO_one ℂ) hc))).congr_left
    intro n
    rw [he n]
    ring
  exact sub_eq_zero.mp (tendsto_nhds_unique (hf.sub ha) (h.trans_tendsto ht))

structure WingStatic (a b c : ℂ) (v : Fin 8 → ℂ) (u : Fin 6 → ℂ) : Prop where
  z_equal : u 3^3=u 4^3
  w_equal : u 1^3=u 2^3
  z_normal : 2*a*u 5^3+c*u 3^3=1
  w_normal : 2*b*u 0^3+c*u 1^3=1
  z_closure : (u 5)⁻¹^2-2*(u 3)⁻¹^2-2*(u 4)⁻¹^2=0
  w_closure : (u 0)⁻¹^2-2*(u 1)⁻¹^2-2*(u 2)⁻¹^2=0
  q1 : v 6=a*u 5^3*(v 6-v 7)+c*u 3^3*(v 6-v 5)
  q2 : v 7=a*u 5^3*(v 7-v 6)+c*u 4^3*(v 7-v 5)
  p3 : v 2=b*u 0^3*(v 2-v 3)+c*u 1^3*(v 2-v 4)
  p4 : v 3=b*u 0^3*(v 3-v 2)+c*u 2^3*(v 3-v 4)
  center_z : b*v 2+b*v 3+c*v 4+2*a*v 0=0
  center_w : 2*b*v 1+c*v 5+a*v 6+a*v 7=0

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (g : ∀ t, PairGauge (q t))
  (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include l hm hd hb ha

theorem actual_wing_static {u : Fin 6 → ℂ} {c : Fin 8 → ℂ} {h : Fin 4 → ℂ}
    (hu : ∀ e, Tendsto (fun t => (q t).delta (wingLeft e) (wingRight e)) atTop (𝓝 (u e)))
    (hun : ∀ e, u e≠0) (hc : ∀ i, Tendsto (fun t => (g t).coeff i) atTop (𝓝 (c i)))
    (hh : ∀ e, Tendsto (fun t => (g t).crossRoot e) atTop (𝓝 (h e))) :
    WingStatic (m 3) (m 0) (m 2) c u := by
  have ht := time_zero l g (long_separations l hm hd).1 (long_separations l hm hd).2 ha
  have ht2 : Tendsto (fun t => (g t).time^2) atTop (𝓝 0) := by simpa using ht.pow 2
  obtain ⟨hm01,hm34⟩ := l.five_body_source19_mass_relation hm hb ha hd
  have U (e : Fin 6) := (hu e).pow 3
  have C (i : Fin 8) := (hc i).isBigO_one ℂ
  have H (e : Fin 4) := ((hh e).pow 3).isBigO_one ℂ
  obtain ⟨hdz,hdw,hnz,hnw,hcz,hcw⟩ := wing_residuals l hm hd g hb ha
  constructor
  · exact sub_eq_zero.mp (tendsto_nhds_unique ((U 3).sub (U 4)) (hdz.trans_tendsto ht2))
  · exact sub_eq_zero.mp (tendsto_nhds_unique ((U 1).sub (U 2)) (hdw.trans_tendsto ht2))
  · exact sub_eq_zero.mp (tendsto_nhds_unique
      ((((U 5).const_mul (2*(m 3:ℂ))).add ((U 3).const_mul (m 2:ℂ))).sub_const 1) (hnz.trans_tendsto ht2))
  · exact sub_eq_zero.mp (tendsto_nhds_unique
      ((((U 0).const_mul (2*(m 0:ℂ))).add ((U 1).const_mul (m 2:ℂ))).sub_const 1) (hnw.trans_tendsto ht2))
  · exact tendsto_nhds_unique ((((hu 5).inv₀ (hun 5)).pow 2 |>.sub
      ((((hu 3).inv₀ (hun 3)).pow 2).const_mul 2)).sub
      ((((hu 4).inv₀ (hun 4)).pow 2).const_mul 2)) (hcz.trans_tendsto ht2)
  · exact tendsto_nhds_unique ((((hu 0).inv₀ (hun 0)).pow 2 |>.sub
      ((((hu 1).inv₀ (hun 1)).pow 2).const_mul 2)).sub
      ((((hu 2).inv₀ (hun 2)).pow 2).const_mul 2)) (hcw.trans_tendsto ht2)
  · apply small_equation_limit (hc 6)
      ((((U 5).const_mul (m 3:ℂ)).mul ((hc 6).sub (hc 7))).add
        (((U 3).const_mul (m 2:ℂ)).mul ((hc 6).sub (hc 5)))) ht
      (((H 0).const_mul_left (-(m 0:ℂ))).add ((H 2).const_mul_left (m 1:ℂ)))
      (bounded_mul ((C 6).sub (C 1)) (((H 0).const_mul_left (m 0:ℂ)).add ((H 2).const_mul_left (m 1:ℂ))))
    intro t; dsimp [wingLeft,wingRight]; simpa only [hm34,mul_assoc] using (g t).small_w3
  · apply small_equation_limit (hc 7)
      ((((U 5).const_mul (m 3:ℂ)).mul ((hc 7).sub (hc 6))).add
        (((U 4).const_mul (m 2:ℂ)).mul ((hc 7).sub (hc 5)))) ht
      (((H 1).const_mul_left (-(m 0:ℂ))).add ((H 3).const_mul_left (m 1:ℂ)))
      (bounded_mul ((C 7).sub (C 1)) (((H 1).const_mul_left (m 0:ℂ)).add ((H 3).const_mul_left (m 1:ℂ))))
    intro t; dsimp [wingLeft,wingRight]; simpa only [mul_assoc] using (g t).small_w4
  · apply small_equation_limit (hc 2)
      ((((U 0).const_mul (m 0:ℂ)).mul ((hc 2).sub (hc 3))).add
        (((U 1).const_mul (m 2:ℂ)).mul ((hc 2).sub (hc 4)))) ht
      (((H 0).const_mul_left (-(m 3:ℂ))).add ((H 1).const_mul_left (m 4:ℂ)))
      (bounded_mul ((C 2).sub (C 0)) (((H 0).const_mul_left (m 3:ℂ)).add ((H 1).const_mul_left (m 4:ℂ))))
    intro t; dsimp [wingLeft,wingRight]; simpa only [hm01,mul_assoc] using (g t).small_z0
  · apply small_equation_limit (hc 3)
      ((((U 0).const_mul (m 0:ℂ)).mul ((hc 3).sub (hc 2))).add
        (((U 2).const_mul (m 2:ℂ)).mul ((hc 3).sub (hc 4)))) ht
      (((H 2).const_mul_left (-(m 3:ℂ))).add ((H 3).const_mul_left (m 4:ℂ)))
      (bounded_mul ((C 3).sub (C 0)) (((H 2).const_mul_left (m 3:ℂ)).add ((H 3).const_mul_left (m 4:ℂ))))
    intro t; dsimp [wingLeft,wingRight]; simpa only [mul_assoc] using (g t).small_z1
  · have hc0 := (((((hc 2).const_mul (m 0:ℂ)).add ((hc 3).const_mul (m 0:ℂ))).add
      ((hc 4).const_mul (m 2:ℂ))).add ((hc 0).const_mul (2*(m 3:ℂ))))
    apply tendsto_nhds_unique hc0
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0)) using 1
    ext t
    have he := (g t).center_z
    simp only [← hm01,← hm34,sub_self,neg_zero,zero_div] at he
    linear_combination he
  · have hc0 := (((((hc 1).const_mul (2*(m 0:ℂ))).add ((hc 5).const_mul (m 2:ℂ))).add
      ((hc 6).const_mul (m 3:ℂ))).add ((hc 7).const_mul (m 3:ℂ)))
    apply tendsto_nhds_unique hc0
    convert (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0)) using 1
    ext t
    have he := (g t).center_w
    simp only [← hm01,← hm34,sub_self,neg_zero,zero_div] at he
    linear_combination he

end CentralConfigurations.FiveBody.D6
