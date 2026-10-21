import CentralConfigurations.FiveBody.ClassifiedSourceCases
import CentralConfigurations.FiveBody.RZeroTransport
import CentralConfigurations.FiveBody.D5CanonicalMetric

/-! Actual twenty-source coverage and sixteen survivors supply one common
role permutation and possible color exchange. The selected original pole,
exact physical level, and complete labelled R product travel together. -/

namespace CentralConfigurations.FiveBody.Classification
noncomputable section
open Filter
open scoped Topology
attribute [local irreducible] DiagramCode.orbit
set_option maxRecDepth 10000

theorem completeRProduct_zero_of_balanced_pole
    {m : Fin 5 → ℝ} (hm : ∀ i, 0 < m i)
    (hremaining : RemainingAnalyticCases m)
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero)
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.potential = (I0 : ℂ))
    (he : FourProductEscapes q) :
    Tendsto (fun t => (q t).toNormalized.fiveBodySelectedProduct (RZero.completeR m))
      atTop (𝓝 0) := by
  obtain ⟨k,hk,horbit,_,_,_⟩ :=
    l.five_body_surviving_source_realization hm hb 0 1 (by decide) ha hz hw
  obtain ⟨e,flip,hcode⟩ := (DiagramCode.mem_orbit_iff _ _).mp horbit
  let qr := fun t => (q t).relabel e
  let lr := l.relabelCanonical e
  have hbr : ∀ t, ‖(qr t).zVector‖ = ‖(qr t).wVector‖ := by
    simpa only [qr,ZWSystem.zVector_norm_relabel,ZWSystem.wVector_norm_relabel] using hb
  have har : Tendsto (fun t => (qr t).inverseScale) atTop (𝓝 0) := by
    simpa only [qr,ZWSystem.inverseScale_relabel] using ha
  have hzr : lr.z.Nonzero := (l.z.nonzero_relabel_iff e).mpr hz
  have hwr : lr.w.Nonzero := (l.w.nonzero_relabel_iff e).mpr hw
  have hphysicalr : PhysicalPotentialLevel (m ∘ e) I0 := D9.physical_level_relabel hphysical e
  have hIr : ∀ t, (qr t).toNormalized.potential = (I0 : ℂ) := by
    intro t
    rw [show (qr t).toNormalized.potential = (q t).toNormalized.potential from D5.potential_relabel (q t) e]
    exact hI t
  have her : FourProductEscapes qr := he.relabel e
  cases flip
  · have hdr : lr.diagramCode = fiveBodySourceDiagram k := by
      change (l.relabelCanonical e).diagramCode = _
      rw [l.diagramCode_relabelCanonical e]
      simpa only [DiagramCode.transform,Bool.false_eq_true,if_false] using hcode
    have hzero := completeRProduct_zero_of_surviving_source hm hremaining e
      lr hbr har hzr hwr hdr hk hphysicalr hIr her
    exact hzero.congr (fun t => RZero.zw_selectedProduct_relabel m hm (q t) e)
  · have has : Tendsto (fun t => ((qr t).swap).inverseScale) atTop (𝓝 0) := by
      change Tendsto (fun t => (‖(qr t).wVector‖ : ℂ)⁻¹) atTop (𝓝 0)
      simpa only [ZWSystem.inverseScale,← hbr] using har
    have hdr : (lr.swapBalanced hbr).diagramCode = fiveBodySourceDiagram k := by
      change DiagramCode.swap (l.relabelCanonical e).diagramCode = _
      rw [l.diagramCode_relabelCanonical e]
      simpa only [DiagramCode.transform,if_true] using hcode
    have hzero := completeRProduct_zero_of_surviving_source hm hremaining e
      (lr.swapBalanced hbr) (fun t => (hbr t).symm) has hwr hzr hdr hk hphysicalr hIr her.swap
    apply hzero.congr
    intro t
    exact (RZero.zw_selectedProduct_swap (m ∘ e) ((q t).relabel e)).trans
      (RZero.zw_selectedProduct_relabel m hm (q t) e)

end
end CentralConfigurations.FiveBody.Classification
