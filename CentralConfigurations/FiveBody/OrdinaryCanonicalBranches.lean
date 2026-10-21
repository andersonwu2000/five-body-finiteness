import CentralConfigurations.FiveBody.OrdinaryCliqueBounds
import CentralConfigurations.FiveBody.OrdinaryTwoTriangleBounds
import CentralConfigurations.FiveBody.OrdinaryD7Exclusion
import CentralConfigurations.Enumeration.OrderRelabelRealization

/-! Public original-sequence endpoints in Chang's common labels. One
permutation acts on both colors and the masses. Color exchange and any
strict subsequence preserve the escaping original factor and exact level. -/

namespace CentralConfigurations.FiveBody.Ordinary
noncomputable section
open Filter
open scoped Topology

theorem not_escaping_of_ak_d10_d16
    {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
    (l : CentralConfigurations.ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : AdmissibleMasses mass)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero)
    {d : Fin 16} (hd : l.diagramCode = akDiagram d)
    (hk : d ∈ ({9,10,11,12,13,14,15} : Finset (Fin 16))) :
    ¬ FourProductEscapes q := by
  by_cases hf : d ∈ ({9,10,11,12} : Finset (Fin 16))
  · exact ScaledZWLimit.d10_d13_not_escaping l hb hd hf ha
  · have hb' : d ∈ ({13,14,15} : Finset (Fin 16)) := by
      fin_cases d <;> simp_all [Fin.ext_iff]
    exact d14_d16_not_escaping l hm hb ha hz hw hd hb'

theorem not_escaping_of_chang_d10_d16
    {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
    (l : CentralConfigurations.ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : AdmissibleMasses mass)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero)
    {d : Fin 16} (hd : l.diagramCode = fiveBodySourceDiagram (changIndex d))
    (hk : d ∈ ({9,10,11,12,13,14,15} : Finset (Fin 16))) :
    ¬ FourProductEscapes q := by
  let e := (akToChang d).symm
  let qr := fun t => (q t).relabel e
  let lr := l.relabelCanonical e
  have hbr : ∀ t, ‖(qr t).zVector‖ = ‖(qr t).wVector‖ := by
    simpa only [qr,ZWSystem.zVector_norm_relabel,ZWSystem.wVector_norm_relabel] using hb
  have har : Tendsto (fun t => (qr t).inverseScale) atTop (𝓝 0) := by
    simpa only [qr,ZWSystem.inverseScale_relabel] using ha
  have hzr : lr.z.Nonzero := (l.z.nonzero_relabel_iff e).mpr hz
  have hwr : lr.w.Nonzero := (l.w.nonzero_relabel_iff e).mpr hw
  have hmr := hm.relabel e
  intro he
  have her : FourProductEscapes qr := he.relabel e
  cases hflip : swapColors d
  · have hdr : lr.diagramCode = akDiagram d := by
      change (l.relabelCanonical e).diagramCode = _
      rw [l.diagramCode_relabelCanonical e,hd]
      simpa only [DiagramCode.transform,hflip,Bool.false_eq_true,if_false,e] using chang_to_ak_identity d
    exact not_escaping_of_ak_d10_d16 lr hmr hbr har hzr hwr hdr hk her
  · have has : Tendsto (fun t => ((qr t).swap).inverseScale) atTop (𝓝 0) := by
      change Tendsto (fun t => (‖(qr t).wVector‖ : ℂ)⁻¹) atTop (𝓝 0)
      simpa only [ZWSystem.inverseScale,← hbr] using har
    have hdr : (lr.swapBalanced hbr).diagramCode = akDiagram d := by
      change DiagramCode.swap (l.relabelCanonical e).diagramCode = _
      rw [l.diagramCode_relabelCanonical e,hd]
      simpa only [DiagramCode.transform,hflip,if_true,e] using chang_to_ak_identity d
    exact not_escaping_of_ak_d10_d16 (lr.swapBalanced hbr) hmr
      (fun t => (hbr t).symm) has hwr hzr hdr hk her.swap

theorem chang4_swap_is_akD7 :
    DiagramCode.swap (fiveBodySourceDiagram 3) = akDiagram 6 := by decide +kernel

theorem not_escaping_of_chang4_physical_potential
    {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    (l : CentralConfigurations.ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0 < m i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (hd : l.diagramCode = fiveBodySourceDiagram 3)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hlevel : ∀ t, (q t).toNormalized.unorderedPotential = (I0 : ℂ)) :
    ¬ FourProductEscapes q := by
  have has : Tendsto (fun t => (q t).swap.inverseScale) atTop (𝓝 0) := by
    change Tendsto (fun t => (‖(q t).wVector‖ : ℂ)⁻¹) atTop (𝓝 0)
    simpa only [ZWSystem.inverseScale,← hb] using ha
  have hds : (l.swapBalanced hb).diagramCode = akDiagram 6 := by
    change DiagramCode.swap l.diagramCode = _
    rw [hd]
    exact chang4_swap_is_akD7
  intro he
  exact D7.not_escaping_of_physical_potential (l.swapBalanced hb) hm
    (fun t => (hb t).symm) hds has hphysical hlevel he.swap

end
end CentralConfigurations.FiveBody.Ordinary
