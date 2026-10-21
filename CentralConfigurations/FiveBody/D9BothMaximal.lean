import CentralConfigurations.FiveBody.D9Orders

namespace CentralConfigurations.FiveBody.D9
open Filter Asymptotics
open scoped Topology

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}

theorem scaled_outer_difference_zero {eps : ℕ → ℂ}
    (heps : Tendsto eps atTop (𝓝 0))
    (hz : (fun t => (q t).z 3 - (q t).z 4) =Θ[atTop] eps)
    {P : ℂ} (hP : P ≠ 0)
    (hd : Tendsto (fun t => (q t).delta 3 4^3) atTop (𝓝 P⁻¹)) :
    Tendsto (fun t => eps t^2*((q t).w 3-(q t).w 4)) atTop (𝓝 0) := by
  have hi : (fun t => ((q t).delta 3 4)⁻¹) =O[atTop] (fun _ => (1 : ℂ)) := by
    apply IsBigO.of_pow (n := 3) (by decide)
    change (fun t => (((q t).delta 3 4)⁻¹)^3) =O[atTop] (fun _ => (1 : ℂ)^3)
    simpa only [one_pow, inv_pow] using
      (hd.inv₀ (inv_ne_zero hP)).isBigO_one ℂ
  have hdiv : (fun t => eps t/((q t).z 3-(q t).z 4)) =O[atTop] (fun _ => (1 : ℂ)) :=
    (isBigO_one_iff ℂ).mpr (div_isBoundedUnder_of_isBigO hz.2)
  have hh := ((hi.pow 2).mul hdiv).mul (isBigO_refl eps atTop)
  have hs : (fun t => eps t^2*((q t).w 3-(q t).w 4)) =O[atTop] eps := by
    apply hh.congr
    · intro t
      have hmetric := (q t).distance 3 4 (by decide)
      have hdelta : (q t).delta 3 4 ≠ 0 := (q t).toNormalized.delta_ne_zero (by decide)
      have hsep := (q t).z_separation_ne_zero (by decide : (3 : Fin 5) ≠ 4)
      field_simp [hdelta, hsep]
      linear_combination -(eps t)^2 * hmetric
    · intro t; simp
  exact hs.trans_tendsto heps

structure BothMaximalOrders (q : ℕ → ZWSystem ℂ 5 mass) where
  eps : ℕ → ℂ
  eps_ne : ∀ t, eps t ≠ 0
  eps_zero : Tendsto eps atTop (𝓝 0)
  limit : ScaledZWLimit q (fun t => eps t^2)
  center : ℕ → ℂ
  z_small : ∀ i : Fin 5, i.val < 3 → (fun t => (q t).z i) =O[atTop] eps
  centered_w_small : ∀ i : Fin 5, i.val < 3 →
    (fun t => (q t).w i - center t) =O[atTop] eps
  exterior_z_small : ∀ i a, Cross i a →
    (fun t => (q t).zForce i a) =O[atTop] (fun t => eps t^2)
  outer_z_separation : (fun t => (q t).z 3 - (q t).z 4) =Θ[atTop] eps
  supported_attachment : limit.w.position 3 ≠ limit.w.position 0
  sparse3 : ∀ j, j ≠ 0 → limit.w.force 3 j = 0
  sparse4 : ∀ j, j ≠ 1 → limit.w.force 4 j = 0
  far_inverse_zero : ∀ i a,
    (i = 0 ∧ a = 4) ∨ (i = 1 ∧ a = 3) ∨ (i = 2 ∧ a = 3) ∨ (i = 2 ∧ a = 4) →
    Tendsto (fun t => (q t).delta i a) atTop (𝓝 0)

theorem BothMaximalOrders.triple_zero (h : BothMaximalOrders q) :
    Tendsto (fun t => triplePotential (q t)) atTop (𝓝 0) := by
  apply D9.triple_zero (c := h.center)
  · intro i hi; exact (h.centered_w_small i hi).trans_tendsto h.eps_zero
  · intro i hi; exact (h.z_small i hi).trans_tendsto h.eps_zero
  · intro i hi
    have hep : Tendsto (fun t => h.eps t^2) atTop (𝓝 0) := by simpa using h.eps_zero.pow 2
    have h3 := (h.exterior_z_small i 3 ⟨hi, by decide⟩).trans_tendsto hep
    have h4 := (h.exterior_z_small i 4 ⟨hi, by decide⟩).trans_tendsto hep
    simpa [exteriorZ] using (h3.const_mul (mass 3)).add (h4.const_mul (mass 4))

theorem BothMaximalOrders.outer_cube (h : BothMaximalOrders q) (hP : mass 3+mass 4 ≠ 0) :
    Tendsto (fun t => (q t).delta 3 4^3) atTop (𝓝 (mass 3+mass 4)⁻¹) := by
  apply outer_cube_limit_of_order h.eps_zero hP h.outer_z_separation
  all_goals intro i hi
  · convert (h.exterior_z_small i 3 ⟨hi, by decide⟩).neg_left using 1
    funext t; dsimp [ZWSystem.zForce]; rw [(q t).delta_symm 3 i]; ring
  · convert (h.exterior_z_small i 4 ⟨hi, by decide⟩).neg_left using 1
    funext t; dsimp [ZWSystem.zForce]; rw [(q t).delta_symm 4 i]; ring

theorem BothMaximalOrders.inner_positions (h : BothMaximalOrders q) (i : Fin 5) (hi : i.val < 3) :
    h.limit.w.position i = h.limit.w.position 0 := by
  have hw := ((h.centered_w_small i hi).trans_tendsto h.eps_zero).sub
    ((h.centered_w_small 0 (by decide)).trans_tendsto h.eps_zero)
  have hz := (h.eps_zero.pow 2).mul hw
  have hl := (h.limit.w_position i).sub (h.limit.w_position 0)
  have hd : Tendsto (fun t => h.eps t^2*(q t).w i-h.eps t^2*(q t).w 0) atTop (𝓝 0) := by
    convert hz using 1
    · funext t; ring
    · ring
  exact sub_eq_zero.mp (tendsto_nhds_unique hl hd)

theorem BothMaximalOrders.outer_positions (h : BothMaximalOrders q) (hP : mass 3+mass 4 ≠ 0) :
    h.limit.w.position 4 = h.limit.w.position 3 := by
  have hz := scaled_outer_difference_zero h.eps_zero h.outer_z_separation hP (h.outer_cube hP)
  have hl := (h.limit.w_position 3).sub (h.limit.w_position 4)
  have hd : Tendsto (fun t => h.eps t^2*(q t).w 3-h.eps t^2*(q t).w 4) atTop (𝓝 0) := by
    simpa only [mul_sub] using hz
  exact (sub_eq_zero.mp (tendsto_nhds_unique hl hd)).symm

theorem BothMaximalOrders.attachment_cubes (h : BothMaximalOrders q)
    (hm0 : mass 0 ≠ 0) (hm1 : mass 1 ≠ 0) (hP : mass 3+mass 4 ≠ 0)
    (hM : mass 0+mass 1+mass 2+mass 3+mass 4 ≠ 0) :
    Tendsto (fun t => (q t).delta 0 3^3) atTop
      (𝓝 ((mass 0+mass 1+mass 2)/((mass 0+mass 1+mass 2+mass 3+mass 4)*mass 0))) ∧
    Tendsto (fun t => (q t).delta 1 4^3) atTop
      (𝓝 ((mass 0+mass 1+mass 2)/((mass 0+mass 1+mass 2+mass 3+mass 4)*mass 1))) :=
  attachment_cube_limits h.limit (fun t => pow_ne_zero 2 (h.eps_ne t)) hm0 hm1 hM
    (h.inner_positions 1 (by decide)) (h.inner_positions 2 (by decide))
    (h.outer_positions hP) h.supported_attachment h.sparse3 h.sparse4

theorem BothMaximalOrders.false_of_physical_potential {m : Fin 5 → ℝ}
    (hm : ∀ i, 0 < m i) {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    (h : BothMaximalOrders q) {I0 : ℝ} (hIpos : 0 < I0)
    (hfloor : ((m 0*m 1+m 0*m 2+m 1*m 2)+
      (m 0+m 1+m 2)*(m 3+m 4)+m 3*m 4)^3 ≤
      (m 0+m 1+m 2+m 3+m 4)*I0^3)
    (hI : ∀ t, (q t).toNormalized.unorderedPotential = (I0 : ℂ)) : False := by
  have h0 := hm 0; have h1 := hm 1; have h2 := hm 2
  have h3 := hm 3; have h4 := hm 4
  have hP : (m 3 : ℂ)+m 4 ≠ 0 := by exact_mod_cast (ne_of_gt (add_pos h3 h4))
  have hM : (m 0 : ℂ)+m 1+m 2+m 3+m 4 ≠ 0 := by
    exact_mod_cast (ne_of_gt (show 0 < m 0+m 1+m 2+m 3+m 4 by positivity))
  have hc := h.attachment_cubes (by exact_mod_cast ne_of_gt h0)
    (by exact_mod_cast ne_of_gt h1) hP hM
  apply false_of_complete_cube_limits hm hIpos hfloor hI h.triple_zero
    (h.far_inverse_zero 0 4 (by simp)) (h.far_inverse_zero 1 3 (by simp))
    (h.far_inverse_zero 2 3 (by simp)) (h.far_inverse_zero 2 4 (by simp))
  · simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul] using hc.1
  · simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_mul] using hc.2
  · simpa only [Complex.ofReal_div, Complex.ofReal_add, Complex.ofReal_one, one_div,
      Complex.ofReal_inv] using h.outer_cube hP

end CentralConfigurations.FiveBody.D9

