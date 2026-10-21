import CentralConfigurations.FiveBody.D5LimitContradiction
import CentralConfigurations.FiveBody.D5Scales
import CentralConfigurations.FiveBody.PhysicalPotentialFloor

namespace CentralConfigurations.FiveBody.D5
open Filter Asymptotics
open scoped Topology BigOperators

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}

theorem false_of_norm_product_violation {e : ℕ → ℂ}
    (hm : ∀ i, 0<m i) (he : ∀ t, e t ≠ 0) (he0 : Tendsto e atTop (𝓝 0))
    (hz : zN q =o[atTop] (fun t => (e t)⁻¹^2))
    (hw : wN q =o[atTop] (fun t => (e t)⁻¹^2))
    (htri : ∀ i : Fin 5, i<3 → Z q i 0 =O[atTop] e ∧ W q i 0 =O[atTop] e)
    {I : ℂ} (hI : ∀ t, (q t).toNormalized.potential=I)
    (hbad : (fun t => (e t)⁻¹) =O[atTop] (fun t => zN q t*wN q t)) : False := by
  obtain ⟨hzs,hws,hprod⟩ := scales_of_violation he he0 hz hw hbad
  obtain ⟨z,w,hzn,hwn,φ,hφ,hzl,hwl⟩ := exists_simultaneous_normalized_subsequence
    (fun t => (q t).z) (fun t => (q t).w) z_positions_ne w_positions_ne
  let qs := q ∘ φ
  let L : PositionLimit qs (zN qs) (wN qs) := {
    z := z
    w := w
    zlim := fun i => by
      have h := ((continuous_apply i).tendsto z).comp hzl
      simpa only [unitNormalize,Pi.smul_apply,smul_eq_mul,div_eq_inv_mul,zN,qs,Function.comp_def] using h
    wlim := fun i => by
      have h := ((continuous_apply i).tendsto w).comp hwl
      simpa only [unitNormalize,Pi.smul_apply,smul_eq_mul,div_eq_inv_mul,wN,qs,Function.comp_def] using h }
  have hcz (i : Fin 5) (hi : i<3) : L.z i=L.z 0 := by
    have hsmall := ((htri i hi).1.trans_isLittleO hzs).comp_tendsto hφ.tendsto_atTop
    have hh := hsmall.tendsto_div_nhds_zero
    have heq := (L.zlim i).sub (L.zlim 0)
    have hzero : Tendsto (fun t => (qs t).z i/zN qs t-(qs t).z 0/zN qs t) atTop (𝓝 0) := by
      simpa only [qs,Z,zN,Function.comp_def,sub_div] using hh
    exact sub_eq_zero.mp (tendsto_nhds_unique heq hzero)
  have hcw (i : Fin 5) (hi : i<3) : L.w i=L.w 0 := by
    have hsmall := ((htri i hi).2.trans_isLittleO hws).comp_tendsto hφ.tendsto_atTop
    have hh := hsmall.tendsto_div_nhds_zero
    have heq := (L.wlim i).sub (L.wlim 0)
    have hzero : Tendsto (fun t => (qs t).w i/wN qs t-(qs t).w 0/wN qs t) atTop (𝓝 0) := by
      simpa only [qs,W,wN,Function.comp_def,sub_div] using hh
    exact sub_eq_zero.mp (tendsto_nhds_unique heq hzero)
  exact L.false_of_collapsed_triple hm zN_ne wN_ne
    (hprod.comp hφ.tendsto_atTop) (fun t => hI (φ t)) hcz hcw hzn hwn

/-- Subsequence exhaustion is part of the proof: every failed little-o bound
produces a preserved positive violation, then two compact unit-position limits. -/
theorem norm_product_small {e : ℕ → ℂ}
    (hm : ∀ i, 0<m i) (he : ∀ t, e t ≠ 0) (he0 : Tendsto e atTop (𝓝 0))
    (hz : zN q =o[atTop] (fun t => (e t)⁻¹^2))
    (hw : wN q =o[atTop] (fun t => (e t)⁻¹^2))
    (htri : ∀ i : Fin 5, i<3 → Z q i 0 =O[atTop] e ∧ W q i 0 =O[atTop] e)
    {I : ℂ} (hI : ∀ t, (q t).toNormalized.potential=I) :
    (fun t => zN q t*wN q t) =o[atTop] (fun t => (e t)⁻¹) := by
  by_contra h
  obtain ⟨φ,hφ,hbad⟩ := exists_subseq_reverse_bigO h
  exact false_of_norm_product_violation (q := q ∘ φ) (e := e ∘ φ)
    hm (fun t => he (φ t)) (he0.comp hφ.tendsto_atTop)
    (hz.comp_tendsto hφ.tendsto_atTop) (hw.comp_tendsto hφ.tendsto_atTop)
    (fun i hi => ⟨((htri i hi).1.comp_tendsto hφ.tendsto_atTop),
      ((htri i hi).2.comp_tendsto hφ.tendsto_atTop)⟩)
    (fun t => hI (φ t)) hbad

/-- Corrected D5 metric endpoint. The exact physical scalar is retained in
the interface; this compact contradiction uses its constancy. -/
theorem metric_small_of_akD5
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0<m i) (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
    (hd : l.diagramCode=akD5Diagram)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I0 : ℝ} (_hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.potential=(I0:ℂ)) (i j : Fin 5) :
    D q i j =o[atTop] (fun t => (eps q t)⁻¹) := by
  have hp := norm_product_small hm eps_ne (eps_zero ha)
    (position_norm_small l hd).1 (position_norm_small l hd).2
    (fun i hi => triangle_orders l hb hd i 0 hi (by decide)) hI
  exact ((z_coordinate_bound i).sub (z_coordinate_bound j)).mul
    ((w_coordinate_bound i).sub (w_coordinate_bound j)) |>.trans_isLittleO hp

end CentralConfigurations.FiveBody.D5
