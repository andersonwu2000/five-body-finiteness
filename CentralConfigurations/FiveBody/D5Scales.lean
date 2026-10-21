import CentralConfigurations.FiveBody.D5Support

namespace CentralConfigurations.FiveBody.D5
open Filter Asymptotics
open scoped Topology BigOperators

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}

noncomputable def zN (q : ℕ → ZWSystem ℂ 5 mass) : ℕ → ℂ := fun t => (‖(q t).z‖ : ℂ)
noncomputable def wN (q : ℕ → ZWSystem ℂ 5 mass) : ℕ → ℂ := fun t => (‖(q t).w‖ : ℂ)

theorem z_positions_ne (t : ℕ) : (q t).z ≠ 0 := by
  intro h
  apply (q t).z_separation_ne_zero (show (0 : Fin 5) ≠ 1 by decide)
  simp [h]

theorem w_positions_ne (t : ℕ) : (q t).w ≠ 0 := by
  intro h
  apply (q t).w_separation_ne_zero (show (0 : Fin 5) ≠ 1 by decide)
  simp [h]

theorem zN_ne (t : ℕ) : zN q t ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (z_positions_ne t))
theorem wN_ne (t : ℕ) : wN q t ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (w_positions_ne t))

theorem z_coordinate_bound (i : Fin 5) : (fun t => (q t).z i) =O[atTop] zN q := by
  refine isBigO_iff.mpr ⟨1,Eventually.of_forall (fun t => ?_)⟩
  simpa [zN] using norm_le_pi_norm ((q t).z) i

theorem w_coordinate_bound (i : Fin 5) : (fun t => (q t).w i) =O[atTop] wN q := by
  refine isBigO_iff.mpr ⟨1,Eventually.of_forall (fun t => ?_)⟩
  simpa [wN] using norm_le_pi_norm ((q t).w) i

theorem position_norm_small
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hd : l.diagramCode=akD5Diagram) :
    zN q =o[atTop] (fun t => (eps q t)⁻¹^2) ∧
    wN q =o[atTop] (fun t => (eps q t)⁻¹^2) := by
  have hz := (isLittleO_pi.mpr (fun i => (positions_small l hd i).1)).norm_left
  have hw := (isLittleO_pi.mpr (fun i => (positions_small l hd i).2)).norm_left
  constructor
  · apply IsLittleO.of_norm_left
    simpa [zN] using hz
  · apply IsLittleO.of_norm_left
    simpa [wN] using hw

/-- A failed little-o estimate retains a fixed positive violation on one
strictly increasing subsequence. No rate or convergence is assumed. -/
theorem exists_subseq_reverse_bigO {f g : ℕ → ℂ} (h : ¬ f =o[atTop] g) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (g ∘ φ) =O[atTop] (f ∘ φ) := by
  rw [isLittleO_iff] at h
  push_neg at h
  obtain ⟨c,hc,hfreq⟩ := h
  obtain ⟨φ,hφ,hφv⟩ := extraction_of_frequently_atTop hfreq
  refine ⟨φ,hφ,isBigO_iff.mpr ⟨c⁻¹,Eventually.of_forall (fun t => ?_)⟩⟩
  have ht := hφv t
  dsimp only [Function.comp_def]
  have hh : ‖g (φ t)‖ < ‖f (φ t)‖/c := (lt_div_iff₀ hc).mpr (by simpa [mul_comm] using ht)
  simpa [div_eq_mul_inv,mul_comm] using hh.le

theorem scales_of_violation {e s r : ℕ → ℂ}
    (he : ∀ t, e t ≠ 0) (he0 : Tendsto e atTop (𝓝 0))
    (hs : s =o[atTop] (fun t => (e t)⁻¹^2))
    (hr : r =o[atTop] (fun t => (e t)⁻¹^2))
    (hbad : (fun t => (e t)⁻¹) =O[atTop] (fun t => s t*r t)) :
    e =o[atTop] s ∧ e =o[atTop] r ∧
      Tendsto (fun t => (s t*r t)⁻¹) atTop (𝓝 0) := by
  have hz : e =o[atTop] s := by
    have h := hbad.trans_isLittleO ((isBigO_refl s atTop).mul_isLittleO hr)
    have hh := h.mul_isBigO (isBigO_refl (fun t => e t^2) atTop)
    convert hh using 1 <;> funext t <;> field_simp [he t]
  have hw : e =o[atTop] r := by
    have h := hbad.trans_isLittleO (hs.mul_isBigO (isBigO_refl r atTop))
    have hh := h.mul_isBigO (isBigO_refl (fun t => e t^2) atTop)
    convert hh using 1 <;> funext t <;> field_simp [he t]
  have hone : (fun _ : ℕ => (1 : ℂ)) =o[atTop] (fun t => (e t)⁻¹) := by
    apply (isLittleO_iff_tendsto (fun t h => (inv_ne_zero (he t) h).elim)).mpr
    simpa only [one_div,inv_inv] using he0
  have hh := (hone.trans_isBigO hbad).tendsto_div_nhds_zero
  exact ⟨hz,hw,by simpa only [one_div] using hh⟩

end CentralConfigurations.FiveBody.D5
