import CentralConfigurations.Asymptotics.ComparableRatioLimits
import CentralConfigurations.Diagrams.TwoRowKiteMass
import CentralConfigurations.Diagrams.QuadrilateralMaximalOrders

/-!
# Two closed rows at a secondary triangle-force scale

The w-forces need not be leading strokes in the original diagram. Their
actual ratios are extracted on a common subsequence. Subtracting the two
physical row equations gives the same kite elimination, including the case
where both normalized positions vanish. Sections 10.2 and 11.8.
-/

namespace CentralConfigurations

open Filter Asymptotics
open scoped Topology BigOperators

theorem ZWSystem.w_position_ratio_limit_two_terms {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (b : ℕ → ℂ) (i j k : Fin n) (hjk : j ≠ k)
    (U V : ℂ)
    (hj : Tendsto (fun t => (q t).wForce i j / b t) atTop (𝓝 U))
    (hk : Tendsto (fun t => (q t).wForce i k / b t) atTop (𝓝 V))
    (ho : ∀ r, r ≠ j → r ≠ k →
      Tendsto (fun t => (q t).wForce i r / b t) atTop (𝓝 0)) :
    Tendsto (fun t => (q t).w i / b t) atTop (𝓝 (mass j * U + mass k * V)) := by
  classical
  let L (r : Fin n) : ℂ := if r = j then U else if r = k then V else 0
  have ht (r : Fin n) : Tendsto (fun t => mass r * ((q t).wForce i r / b t))
      atTop (𝓝 (mass r * L r)) := by
    apply tendsto_const_nhds.mul
    by_cases hrj : r = j
    · subst r; simpa [L] using hj
    by_cases hrk : r = k
    · subst r; simpa [L, hrj] using hk
    · simpa [L, hrj, hrk] using ho r hrj hrk
  have hs := tendsto_finsetSum Finset.univ (fun r _ => ht r)
  have heq (t : ℕ) : (∑ r, mass r * ((q t).wForce i r / b t)) = (q t).w i / b t := by
    rw [(q t).force_w i, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro r _
    dsimp [ZWSystem.wForce]
    ring
  have hL : (∑ r, mass r * L r) = mass j * U + mass k * V := by
    have hp (r : Fin n) : mass r * L r =
        (if r = j then mass j * U else 0) + (if r = k then mass k * V else 0) := by
      by_cases hrj : r = j <;> by_cases hrk : r = k <;> simp_all [L]
    simp_rw [hp, Finset.sum_add_distrib]
    simp
  simpa only [heq, hL] using hs

namespace PairEstimateData

theorem wForce_littleO_of_small_zForce (p r : PairEstimateData)
    (hf : p.zForce =o[atTop] r.zForce) (hz : r.z =O[atTop] p.z) :
    p.wForce =o[atTop] r.wForce := by
  have hi := hz.inv_rev (Eventually.of_forall fun t h => (r.z_ne_zero t h).elim)
  have h := hf.mul_isBigO (hi.pow 4)
  have hcube : (fun t => p.wForce t ^ 3) =o[atTop] (fun t => r.wForce t ^ 3) :=
    h.congr (fun t => (p.swap.zForce_cube_opposite t).symm)
      (fun t => (r.swap.zForce_cube_opposite t).symm)
  exact hcube.of_pow (by decide : (3 : ℕ) ≠ 0)

end PairEstimateData

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℝ}
  {q : ℕ → ZWSystem ℂ n (fun a => (mass a : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))

theorem uncircled_z_edge_w_separation_div_force_zero (i j : Fin n) (hij : i ≠ j)
    (hzi : l.z.position i = 0) (hzj : l.z.position j = 0) (hz : l.z.force i j ≠ 0) :
    Tendsto (fun t => ((q t).w i - (q t).w j) / (q t).wForce i j) atTop (𝓝 0) := by
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) i j hij
  have hsep : Tendsto (fun t => (q t).inverseScale * ((q t).z i - (q t).z j))
      atTop (𝓝 0) := by
    simpa only [hzi, hzj, sub_self, mul_sub] using (l.z_position i).sub (l.z_position j)
  have h := tendsto_ratio_of_scaled hs hz hsep (l.z_force i j)
  simp only [zero_div] at h
  convert h using 1
  funext t
  apply (div_eq_div_iff ((q t).wForce_ne_zero i j hij) ((q t).zForce_ne_zero i j hij)).mpr
  dsimp [ZWSystem.zForce, ZWSystem.wForce]
  ring

theorem secondary_triangle_rows_mass_polynomial
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (hm : ∀ a, 0 < mass a) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzi : l.z.position i = 0) (hzj : l.z.position j = 0)
    (hzij : l.z.force i j ≠ 0) (hzik : l.z.force i k ≠ 0) (hzjk : l.z.force j k ≠ 0)
    (hzci : ∀ r, r ≠ j → r ≠ k → l.z.force i r = 0)
    (hzcj : ∀ r, r ≠ i → r ≠ k → l.z.force j r = 0)
    (hwci : ∀ r, r ≠ j → r ≠ k →
      (fun t => (q t).wForce i r) =o[atTop] (fun t => (q t).wForce i j))
    (hwcj : ∀ r, r ≠ i → r ≠ k →
      (fun t => (q t).wForce j r) =o[atTop] (fun t => (q t).wForce i j)) :
    kiteMassPolynomial (mass i) (mass j) (mass k) = 0 := by
  have hmi : (mass i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm i))
  have hmj : (mass j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm j))
  have hmk : (mass k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm k))
  have hZ := l.z.two_term_force_ratios i j k hik hjk hmk hzij hzi hzj hzci hzcj
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) i j hij
  have hZu := tendsto_ratio_of_scaled hs hzij (l.z_force i k) (l.z_force i j)
  have hZv := tendsto_ratio_of_scaled hs hzij (l.z_force j k) (l.z_force i j)
  rw [hZ.1] at hZu
  rw [hZ.2] at hZv
  have hzorders := l.z_triangle_orders hb i j k hij hjk hik hzij hzjk hzik
  have hWu := l.wForce_theta_of_z_separation_strokes hb i k i j hik hij hzik hzij hzorders.2.1.symm
  have hWv := l.wForce_theta_of_z_separation_strokes hb j k i j hjk hij hzjk hzij hzorders.1.symm
  obtain ⟨U, V, hU, hV, φ, hφ, hlimU, hlimV⟩ := exists_two_nonzero_ratio_limits
    (fun t => (q t).wForce_ne_zero i j hij) hWu hWv
  have hself : Tendsto (fun t => (q (φ t)).wForce i j / (q (φ t)).wForce i j)
      atTop (𝓝 1) := by
    simpa only [div_self ((q (φ _)).wForce_ne_zero i j hij)] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 1))
  have hreverse : Tendsto (fun t => (q (φ t)).wForce j i / (q (φ t)).wForce i j)
      atTop (𝓝 (-1)) := by
    convert hself.neg using 1
    funext t
    rw [show (q (φ t)).wForce j i = -(q (φ t)).wForce i j from
      (q (φ t)).swap.zForce_antisymm j i, neg_div]
  have hpi := ZWSystem.w_position_ratio_limit_two_terms (q ∘ φ)
    (fun t => (q (φ t)).wForce i j) i j k hjk 1 U hself hlimU
    (fun r hrj hrk => ((hwci r hrj hrk).tendsto_div_nhds_zero).comp hφ.tendsto_atTop)
  have hpj := ZWSystem.w_position_ratio_limit_two_terms (q ∘ φ)
    (fun t => (q (φ t)).wForce i j) j i k hik (-1) V hreverse hlimV
    (fun r hri hrk => ((hwcj r hri hrk).tendsto_div_nhds_zero).comp hφ.tendsto_atTop)
  have hdiff := (l.uncircled_z_edge_w_separation_div_force_zero i j hij hzi hzj hzij).comp
    hφ.tendsto_atTop
  have heq : ((mass j : ℂ) * 1 + (mass k : ℂ) * U) -
      ((mass i : ℂ) * (-1) + (mass k : ℂ) * V) = 0 := by
    exact tendsto_nhds_unique (by simpa only [sub_div] using hpi.sub hpj) hdiff
  have hbalance : V - U = ((mass i : ℂ) + (mass j : ℂ)) / (mass k : ℂ) := by
    field_simp [hmk]
    linear_combination -heq
  have hu : -(mass j : ℂ) / (mass k : ℂ) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hmj) hmk
  have hv : (mass i : ℂ) / (mass k : ℂ) ≠ 0 := div_ne_zero hmi hmk
  obtain ⟨x, y, hx, hy, hsz, hsw⟩ := two_color_triangle_force_ratio_roots (q ∘ φ) i j k hij hik hjk
    (-(mass j : ℂ) / (mass k : ℂ)) ((mass i : ℂ) / (mass k : ℂ)) U V hu hv hU hV
    (hZu.comp hφ.tendsto_atTop) hlimU (hZv.comp hφ.tendsto_atTop) hlimV
  obtain ⟨t, hF, hG⟩ := kite_equations_of_roots (mass i : ℂ) (mass j : ℂ) (mass k : ℂ)
    x y U V hmi hmj hmk hU hV hx hy hsz hsw hbalance
  exact kite_mass_polynomial_of_equations (mass i) (mass j) (mass k)
    (hm i) (hm j) (hm k) t hF hG

/-- A w-stroke from the pivot k to an external vertex puts that vertex at
negligible z-distance from k relative to a single z-edge i-k. A missing
external z-stroke then makes the external w-force negligible as well. -/
theorem single_z_edge_w_pivot_external_force_small
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i k r : Fin n) (hik : i ≠ k) (hir : i ≠ r) (hkr : k ≠ r)
    (hz : l.z.force i k ≠ 0) (hw : l.w.force i k = 0)
    (hwr : l.w.force k r ≠ 0) (hzr : l.z.force i r = 0) :
    (fun t => (q t).wForce i r) =o[atTop] (fun t => (q t).wForce i k) := by
  let p := ZWSystem.pairEstimateData q hb i k hik
  let s := ZWSystem.pairEstimateData q hb k r hkr
  let e := ZWSystem.pairEstimateData q hb i r hir
  have hp := p.single_z_separations ((l.pair_z_stroke_iff hb i k hik).mpr hz)
    ((l.pair_w_absent_iff hb i k hik).mpr hw)
  have hs := s.swap.stroke_w_upper ((l.pair_w_stroke_iff hb k r hkr).mpr hwr)
  have hsmall : (fun t => (q t).z r - (q t).z k) =o[atTop]
      (fun t => (q t).z k - (q t).z i) := by
    exact (hs.trans_isLittleO hp.1).neg_left.neg_right.congr
      (fun t => by change -((q t).z k - (q t).z r) = _; ring)
      (fun t => by change -((q t).z i - (q t).z k) = _; ring)
  have htheta := separation_theta_of_littleO hsmall
  have horder : p.z =O[atTop] e.z := by
    simpa only [isBigO_iff, norm_sub_rev] using htheta.1
  exact e.wForce_littleO_of_small_zForce p
    (l.zForce_littleO_of_absent_stroke hb i r i k hir hik hzr hz) horder

theorem secondary_triangle_w_pivot_mass_polynomial
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (hm : ∀ a, 0 < mass a) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzi : l.z.position i = 0) (hzj : l.z.position j = 0)
    (hzij : l.z.force i j ≠ 0) (hzik : l.z.force i k ≠ 0) (hzjk : l.z.force j k ≠ 0)
    (hwik : l.w.force i k = 0) (hwjk : l.w.force j k = 0)
    (hzci : ∀ r, r ≠ j → r ≠ k → l.z.force i r = 0)
    (hzcj : ∀ r, r ≠ i → r ≠ k → l.z.force j r = 0)
    (hpivot : ∀ r, r ≠ i → r ≠ j → r ≠ k → l.w.force k r ≠ 0) :
    kiteMassPolynomial (mass i) (mass j) (mass k) = 0 := by
  have hzorders := l.z_triangle_orders hb i j k hij hjk hik hzij hzjk hzik
  have hWu := l.wForce_theta_of_z_separation_strokes hb i k i j hik hij hzik hzij hzorders.2.1.symm
  have hWv := l.wForce_theta_of_z_separation_strokes hb j k i j hjk hij hzjk hzij hzorders.1.symm
  apply l.secondary_triangle_rows_mass_polynomial hb hm i j k hij hik hjk hzi hzj
    hzij hzik hzjk hzci hzcj
  · intro r hrj hrk
    by_cases hri : r = i
    · subst r
      simpa only [ZWSystem.wForce, sub_self, mul_zero] using
        (isLittleO_zero (fun t => (q t).wForce i j) atTop)
    · exact (l.single_z_edge_w_pivot_external_force_small hb i k r hik (Ne.symm hri)
        (Ne.symm hrk) hzik hwik (hpivot r hri hrj hrk) (hzci r hrj hrk)).trans_isBigO hWu.1
  · intro r hri hrk
    by_cases hrj : r = j
    · subst r
      simpa only [ZWSystem.wForce, sub_self, mul_zero] using
        (isLittleO_zero (fun t => (q t).wForce i j) atTop)
    · exact (l.single_z_edge_w_pivot_external_force_small hb j k r hjk (Ne.symm hrj)
        (Ne.symm hrk) hzjk hwjk (hpivot r hri hrj hrk) (hzcj r hri hrk)).trans_isBigO hWv.1

theorem secondary_triangle_w_pivot_mass_of_code {d : DiagramCode n}
    (hd : l.diagramCode = d)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (hm : ∀ a, 0 < mass a) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hdiag : d.1 (upperIndex i i) = false ∧ d.1 (upperIndex j j) = false)
    (hzij : d.1 (upperIndex i j) = true)
    (hzik : d.1 (upperIndex i k) = true) (hzjk : d.1 (upperIndex j k) = true)
    (hwik : d.2 (upperIndex i k) = false) (hwjk : d.2 (upperIndex j k) = false)
    (hzci : ∀ r, r ≠ j → r ≠ k → d.1 (upperIndex i r) = false)
    (hzcj : ∀ r, r ≠ i → r ≠ k → d.1 (upperIndex j r) = false)
    (hpivot : ∀ r, r ≠ i → r ≠ j → r ≠ k → d.2 (upperIndex k r) = true) :
    kiteMassPolynomial (mass i) (mass j) (mass k) = 0 :=
  l.secondary_triangle_w_pivot_mass_polynomial hb hm i j k hij hik hjk
    (l.z_position_zero_of_code hd i hdiag.1) (l.z_position_zero_of_code hd j hdiag.2)
    (l.z_force_ne_zero_of_code hd i j hij hzij)
    (l.z_force_ne_zero_of_code hd i k hik hzik) (l.z_force_ne_zero_of_code hd j k hjk hzjk)
    (l.w_force_zero_of_code hd i k hwik) (l.w_force_zero_of_code hd j k hwjk)
    (fun r hrj hrk => l.z_force_zero_of_code hd i r (hzci r hrj hrk))
    (fun r hri hrk => l.z_force_zero_of_code hd j r (hzcj r hri hrk))
    (fun r hri hrj hrk => l.w_force_ne_zero_of_code hd k r (Ne.symm hrk) (hpivot r hri hrj hrk))

end ScaledZWLimit
end CentralConfigurations
