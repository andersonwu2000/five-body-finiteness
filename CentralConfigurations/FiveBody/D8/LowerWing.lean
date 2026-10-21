import CentralConfigurations.FiveBody.D8.CrossCompatibility

namespace CentralConfigurations.FiveBody.D8
open Filter Asymptotics
open scoped Topology

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 6)
include l hm hd

theorem exists_lower_root_limits : ∃ E F G : ℂ, E≠0 ∧ F≠0 ∧ G≠0 ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
    Tendsto (fun t => (q (φ t)).delta 0 1) atTop (𝓝 E) ∧
    Tendsto (fun t => (q (φ t)).delta 0 4) atTop (𝓝 F) ∧
    Tendsto (fun t => (q (φ t)).delta 1 4) atTop (𝓝 G) := by
  obtain ⟨⟨e,hen,he⟩,⟨f,hfn,hf⟩,⟨g,hgn,hg⟩⟩ := lower_cube_limits l hm hd
  let r : ℕ → Fin 3 → ℂ := fun t => ![(q t).delta 0 1,(q t).delta 0 4,(q t).delta 1 4]
  have hb (i : Fin 3) : Bornology.IsBounded (Set.range (fun t => r t i)) := by
    fin_cases i
    · exact bounded_of_power_tendsto (by decide : 3≠0) he
    · exact bounded_of_power_tendsto (by decide : 3≠0) hf
    · exact bounded_of_power_tendsto (by decide : 3≠0) hg
  obtain ⟨v,φ,hφ,hv⟩ := exists_finite_coordinate_limits r hb
  have h0 : v 0^3=e := tendsto_nhds_unique ((hv 0).pow 3) (he.comp hφ.tendsto_atTop)
  have h1 : v 1^3=f := tendsto_nhds_unique ((hv 1).pow 3) (hf.comp hφ.tendsto_atTop)
  have h2 : v 2^3=g := tendsto_nhds_unique ((hv 2).pow 3) (hg.comp hφ.tendsto_atTop)
  refine ⟨v 0,v 1,v 2,?_,?_,?_,φ,hφ,hv 0,hv 1,hv 2⟩
  · intro h; rw [h,zero_pow (by decide : 3≠0)] at h0; exact hen h0.symm
  · intro h; rw [h,zero_pow (by decide : 3≠0)] at h1; exact hfn h1.symm
  · intro h; rw [h,zero_pow (by decide : 3≠0)] at h2; exact hgn h2.symm

theorem lower_opposite_positions (hab : m 0=m 1) : l.w.position 1= -l.w.position 0 := by
  have h := lower_balance l hm hd
  have hn : (m 0:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 0)
  apply (mul_left_cancel₀ hn)
  rw [← hab] at h
  linear_combination h

theorem w_force_limit_from_root (i j : Fin 5) {v : ℂ}
    (hv : Tendsto (fun t => (q t).delta i j) atTop (𝓝 v)) :
    l.w.force i j=v^3*(l.w.position i-l.w.position j) := by
  have h := (hv.pow 3).mul ((l.w_position i).sub (l.w_position j))
  have he : Tendsto (fun t => (q t).inverseScale*(q t).wForce i j) atTop
      (𝓝 (v^3*(l.w.position i-l.w.position j))) := h.congr (fun t => by dsimp [ZWSystem.wForce]; ring)
  exact tendsto_nhds_unique (l.w_force i j) he

theorem lower_force_equations (hab : m 0=m 1) {E F G : ℂ}
    (hE : Tendsto (fun t => (q t).delta 0 1) atTop (𝓝 E))
    (hF : Tendsto (fun t => (q t).delta 0 4) atTop (𝓝 F))
    (hG : Tendsto (fun t => (q t).delta 1 4) atTop (𝓝 G)) :
    2*(m 0:ℂ)*E^3+(m 4:ℂ)*F^3=1 ∧ F^3=G^3 := by
  have hw1 := lower_opposite_positions l hm hd hab
  have hw4 := (leading_positions l hm hd).2.2.2.1
  have hw0 := (leading_positions l hm hd).2.2.2.2.1
  have he := w_force_limit_from_root l hm hd 0 1 hE
  have hf := w_force_limit_from_root l hm hd 0 4 hF
  have hg := w_force_limit_from_root l hm hd 1 4 hG
  have h02 := l.w_force_zero_of_code hd 0 2 (by decide +kernel)
  have h03 := l.w_force_zero_of_code hd 0 3 (by decide +kernel)
  have h42 := l.w_force_zero_of_code hd 4 2 (by decide +kernel)
  have h43 := l.w_force_zero_of_code hd 4 3 (by decide +kernel)
  have hB0 := l.w.balance 0
  have hB4 := l.w.balance 4
  simp [Fin.sum_univ_succ,l.w.diagonal,h02,h03,he,hf,hw1,hw4,← hab] at hB0
  simp [Fin.sum_univ_succ,l.w.diagonal,h42,h43,l.w.antisymm 4 0,l.w.antisymm 4 1,hf,hg,hw1,hw4,← hab] at hB4
  constructor
  · apply (mul_right_cancel₀ hw0)
    linear_combination -hB0
  · have hn : (m 0:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 0)
    apply (mul_left_cancel₀ (mul_ne_zero hn hw0))
    linear_combination hB4

omit l hm hd in
theorem metric_scaled_inverse (i j : Fin 5) (hij : i≠j) (t : ℕ) :
    ((q t).delta i j)⁻¹^2/((q t).inverseScale*((q t).w i-(q t).w j))=
      ((q t).z i-(q t).z j)/(q t).inverseScale := by
  have h := (q t).distance i j hij
  field_simp [(q t).delta_ne_zero i j hij,(q t).w_separation_ne_zero hij,
    ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t]
  linear_combination -h

theorem lower_metric_closure (hab : m 0=m 1) {E F G : ℂ} (hEn : E≠0) (hFn : F≠0) (hGn : G≠0)
    (hE : Tendsto (fun t => (q t).delta 0 1) atTop (𝓝 E))
    (hF : Tendsto (fun t => (q t).delta 0 4) atTop (𝓝 F))
    (hG : Tendsto (fun t => (q t).delta 1 4) atTop (𝓝 G)) :
    E⁻¹^2-2*F⁻¹^2-2*G⁻¹^2=0 := by
  have hw1 := lower_opposite_positions l hm hd hab
  have hw4 := (leading_positions l hm hd).2.2.2.1
  have hw0 := (leading_positions l hm hd).2.2.2.2.1
  have hw (i j : Fin 5) : Tendsto (fun t => (q t).inverseScale*((q t).w i-(q t).w j)) atTop
      (𝓝 (l.w.position i-l.w.position j)) := by simpa only [mul_sub] using (l.w_position i).sub (l.w_position j)
  have h01 : l.w.position 0-l.w.position 1≠0 := by rw [hw1,sub_neg_eq_add,← two_mul]; exact mul_ne_zero (by norm_num) hw0
  have h04 : l.w.position 0-l.w.position 4≠0 := by simpa only [hw4,sub_zero] using hw0
  have h14 : l.w.position 1-l.w.position 4≠0 := by simpa only [hw1,hw4,sub_zero] using neg_ne_zero.mpr hw0
  have hlim := ((((hE.inv₀ hEn).pow 2).div (hw 0 1) h01).sub (((hF.inv₀ hFn).pow 2).div (hw 0 4) h04)).add
    (((hG.inv₀ hGn).pow 2).div (hw 1 4) h14)
  have he : E⁻¹^2/(l.w.position 0-l.w.position 1)-F⁻¹^2/(l.w.position 0-l.w.position 4)+G⁻¹^2/(l.w.position 1-l.w.position 4)=0 := by
    apply tendsto_nhds_unique hlim
    have heq : (fun t => ((q t).delta 0 1)⁻¹^2/((q t).inverseScale*((q t).w 0-(q t).w 1))-
      ((q t).delta 0 4)⁻¹^2/((q t).inverseScale*((q t).w 0-(q t).w 4))+
      ((q t).delta 1 4)⁻¹^2/((q t).inverseScale*((q t).w 1-(q t).w 4)))=(fun _ => (0:ℂ)) := by
      ext t
      rw [metric_scaled_inverse 0 1 (by decide),metric_scaled_inverse 0 4 (by decide),metric_scaled_inverse 1 4 (by decide)]
      ring
    exact (tendsto_const_nhds (x := (0:ℂ))).congr (fun t => (congrFun heq t).symm)
  calc
    _ = 2*l.w.position 0*(E⁻¹^2/(l.w.position 0-l.w.position 1)-F⁻¹^2/(l.w.position 0-l.w.position 4)+G⁻¹^2/(l.w.position 1-l.w.position 4)) := by
      rw [hw1,hw4]
      field_simp [hw0]
      ring
    _ = 0 := by rw [he,mul_zero]

end CentralConfigurations.FiveBody.D8
