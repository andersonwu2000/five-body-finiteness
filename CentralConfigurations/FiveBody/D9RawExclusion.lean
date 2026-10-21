import CentralConfigurations.FiveBody.D9OrderConstructors

namespace CentralConfigurations.FiveBody.D9Raw
open Filter
open scoped Topology BigOperators
open D9Bridge

def armSwap : Equiv.Perm (Fin 5) where
  toFun i := ![1,0,2,4,3] i
  invFun i := ![1,0,2,4,3] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem armSwap_preserves_code : DiagramCode.relabel akD9Diagram armSwap = akD9Diagram := by
  decide +kernel

theorem relabel_identity {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) :
    q.relabel (Equiv.refl (Fin 5)) = q := by cases q; rfl

/-- The normalized leading positions already make the attachment split
exhaustive.  No extra rate selection or Puiseux parameter is introduced. -/
theorem exists_attachment_orders {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (hd : l.diagramCode = akD9Diagram)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hM : (∑ i, mass i) ≠ 0) :
    ∃ e : Equiv.Perm (Fin 5), Nonempty (D9.AttachmentOrders (fun t => (q t).relabel e)) := by
  have hone := at_least_one_maximal_attachment l hd ha hM
  by_cases h03 : l.w.position 3 ≠ l.w.position 0
  · by_cases h14 : l.w.position 4 ≠ l.w.position 1
    · refine ⟨Equiv.refl _, ?_⟩
      simpa only [relabel_identity] using
        (show Nonempty (D9.AttachmentOrders q) from
          ⟨.bothMaximal (bothMaximalOrders l hb hd ha hM h03 h14)⟩)
    · have h14eq := not_ne_iff.mp h14
      let lr := l.relabelCanonical armSwap
      have hdr : lr.diagramCode = akD9Diagram := by
        rw [ScaledZWLimit.diagramCode_relabelCanonical, hd, armSwap_preserves_code]
      have hbr : ∀ t, ‖((q t).relabel armSwap).zVector‖ = ‖((q t).relabel armSwap).wVector‖ := by
        simpa only [ZWSystem.zVector_norm_relabel, ZWSystem.wVector_norm_relabel] using hb
      have har : Tendsto (fun t => ((q t).relabel armSwap).inverseScale) atTop (𝓝 0) := by
        simpa only [ZWSystem.inverseScale_relabel] using ha
      have hMr : (∑ i, mass (armSwap i)) ≠ 0 := by
        simpa only [Equiv.sum_comp armSwap mass] using hM
      have hr03 : lr.w.position 3 = lr.w.position 0 := h14eq
      have hr14 : lr.w.position 4 ≠ lr.w.position 1 := h03
      exact ⟨armSwap, ⟨.skew (skewOrders lr hbr hdr har hMr hr03 hr14)⟩⟩
  · have h03eq := not_ne_iff.mp h03
    have h14 := hone.resolve_left h03
    refine ⟨Equiv.refl _, ?_⟩
    simpa only [relabel_identity] using
      (show Nonempty (D9.AttachmentOrders q) from
        ⟨.skew (skewOrders l hb hd ha hM h03eq h14)⟩)

theorem zw_ext {mass : Fin 5 → ℂ} {q r : ZWSystem ℂ 5 mass}
    (hz : q.z = r.z) (hw : q.w = r.w) (hd : q.delta = r.delta) : q = r := by
  cases q; cases r
  cases hz; cases hw; cases hd
  rfl

theorem inRoles_false_eq_relabel {m : Fin 5 → ℝ}
    (q : ZWSystem ℂ 5 (fun i => (m i : ℂ))) (e : Equiv.Perm (Fin 5)) :
    D9.inRoles q e false = q.relabel e := by
  apply zw_ext
  · funext i
    exact q.toNormalized_toZW_z (e i)
  · funext i
    exact q.toNormalized_toZW_w (e i)
  · rfl

/-- Complete bridge from an actual balanced canonical Chang diagram 12
limit to the D9 attachment-order interface. All order fields
are derived from the support. The original sequence is retained (identity subsequence). -/
theorem hasExtractedAttachmentOrders_of_chang12 {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0 < m i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (hd : l.diagramCode = fiveBodySourceDiagram 11)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    D9.HasExtractedAttachmentOrders q := by
  let lc := l.relabelCanonical canonicalToAKRoles
  have hdc : lc.diagramCode = akD9Diagram :=
    ScaledZWLimit.chang12_relabel_to_akD9 l hd
  have hbc : ∀ t, ‖((q t).relabel canonicalToAKRoles).zVector‖ =
      ‖((q t).relabel canonicalToAKRoles).wVector‖ := by
    simpa only [ZWSystem.zVector_norm_relabel, ZWSystem.wVector_norm_relabel] using hb
  have hac : Tendsto (fun t => ((q t).relabel canonicalToAKRoles).inverseScale) atTop (𝓝 0) := by
    simpa only [ZWSystem.inverseScale_relabel] using ha
  have hMc : (∑ i, (m (canonicalToAKRoles i) : ℂ)) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.sum_pos (fun i _ => hm (canonicalToAKRoles i)) Finset.univ_nonempty))
  obtain ⟨e, he⟩ := exists_attachment_orders lc hbc hdc hac hMc
  refine ⟨id, strictMono_id, e.trans canonicalToAKRoles, false, ?_⟩
  convert he using 1
  congr 1
  funext t
  rw [inRoles_false_eq_relabel]
  rfl

/-- D9 exclusion at a physical potential level, from canonical diagram
support and the usual balanced singular-limit assumptions. -/
theorem false_of_chang12_physical_potential {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0 < m i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (hd : l.diagramCode = fiveBodySourceDiagram 11)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.potential = (I0 : ℂ)) : False := by
  apply D9.false_of_extracted_attachment_orders hm hphysical
    (fun t => (q t).toNormalized.potential_eq_unordered.symm.trans (hI t))
    (hasExtractedAttachmentOrders_of_chang12 l hm hb hd ha)

end CentralConfigurations.FiveBody.D9Raw
