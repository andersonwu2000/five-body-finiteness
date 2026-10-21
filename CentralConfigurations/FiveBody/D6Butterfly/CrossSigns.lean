import CentralConfigurations.FiveBody.D6Butterfly.Translations

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

theorem coefficient_zero {t : ℕ → ℂ} {c : ℂ} (ht : Tendsto t atTop (𝓝 0))
    (htn : ∀ n, t n≠0) (k : ℕ)
    (h : (fun n => c*t n^k) =O[atTop] (fun n => t n^(k+1))) : c=0 := by
  have hh := h.mul (isBigO_refl (fun n => (t n^k)⁻¹) atTop)
  have hsmall : (fun _ : ℕ => c) =O[atTop] t := by
    apply hh.congr
    · intro n; field_simp [htn n]
    · intro n; rw [pow_succ]; field_simp [htn n]
  exact tendsto_nhds_unique tendsto_const_nhds (hsmall.trans_tendsto ht)

theorem translations_equal {f g t : ℕ → ℂ} {F G D E : ℂ}
    (ht : Tendsto t atTop (𝓝 0)) (htn : ∀ n, t n≠0)
    (hf : (fun n => f n-F-t n*D) =O[atTop] (fun n => t n^2))
    (hg : (fun n => g n-G-t n*E) =O[atTop] (fun n => t n^2))
    (hfg : (fun n => (f n-g n)-(F-G)) =O[atTop] (fun n => t n^2)) : D=E := by
  apply sub_eq_zero.mp
  apply coefficient_zero ht htn 1
  exact (hfg.sub (hf.sub hg)).congr_left (fun n => by ring)

theorem four_cross_signs (h : Fin 4 → ℂ)
    (hs : ∀ e, h e^2=crossSign e)
    (ht : h 0^3+h 3^3-h 1^3-h 2^3=0) : h 3= -h 0 ∧ h 1= -h 2 := by
  have h0 : h 0=Complex.I ∨ h 0= -Complex.I :=
    eq_or_eq_neg_of_sq_eq_sq _ _ (by rw [hs 0,Complex.I_sq]; rfl)
  have h3 : h 3=Complex.I ∨ h 3= -Complex.I :=
    eq_or_eq_neg_of_sq_eq_sq _ _ (by rw [hs 3,Complex.I_sq]; rfl)
  have h1 : h 1=1 ∨ h 1= -1 := eq_or_eq_neg_of_sq_eq_sq _ _ (by rw [hs 1]; change (1:ℂ)=(1:ℂ)^2; norm_num)
  have h2 : h 2=1 ∨ h 2= -1 := eq_or_eq_neg_of_sq_eq_sq _ _ (by rw [hs 2]; change (1:ℂ)=(1:ℂ)^2; norm_num)
  rcases h0 with h0|h0 <;> rcases h3 with h3|h3 <;>
    rcases h1 with h1|h1 <;> rcases h2 with h2|h2 <;>
    simp_all [pow_succ]
  all_goals have hr := congrArg Complex.re ht
  all_goals norm_num at hr

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (g : ∀ t, PairGauge (q t))
  (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include l hm hd hb ha

theorem actual_cross_signs {u : Fin 6 → ℂ} {c : Fin 8 → ℂ} {h : Fin 4 → ℂ}
    (hu : ∀ e, Tendsto (fun t => (q t).delta (wingLeft e) (wingRight e)) atTop (𝓝 (u e)))
    (hun : ∀ e, u e≠0) (hc : ∀ i, Tendsto (fun t => (g t).coeff i) atTop (𝓝 (c i)))
    (hh : ∀ e, Tendsto (fun t => (g t).crossRoot e) atTop (𝓝 (h e))) :
    h 3= -h 0 ∧ h 1= -h 2 := by
  have ht := time_zero l g (long_separations l hm hd).1 (long_separations l hm hd).2 ha
  obtain ⟨h6,h7,-,-⟩ := outer_translation_orders l hm hd g hb ha hu hun hc hh
  obtain ⟨hq1,hq2,-,-⟩ := short_difference_orders l hm hd g hb ha hu hun hc
  have he := translations_equal ht (fun n => (g n).time_ne) h6 h7
    ((hq1.sub hq2).congr_left (fun n => by ring))
  obtain ⟨hm01,-⟩ := l.five_body_source19_mass_relation hm hb ha hd
  have hn : (m 0:ℂ)≠0 := by exact_mod_cast ne_of_gt (hm 0)
  have hsign e := (cross_root_rigidity l hm hd g hb ha e (hh e)).1
  apply four_cross_signs h hsign
  rw [← hm01] at he
  apply (mul_left_cancel₀ hn)
  linear_combination -he

end CentralConfigurations.FiveBody.D6

