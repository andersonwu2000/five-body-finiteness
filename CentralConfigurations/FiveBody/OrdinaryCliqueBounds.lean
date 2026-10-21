import CentralConfigurations.FiveBody.OrdinaryDiagramIdentity
import CentralConfigurations.FiveBody.FourProductBounds

/-! D14--D16 are excluded at a pole of an original four-product. The
already proved actual order extraction and collapsing-complement theorem
are used with their full premises; no AK Proposition 3 or 8 is imported. -/

namespace CentralConfigurations.FiveBody.Ordinary
noncomputable section
open Filter
open scoped Topology

theorem d14_d16_complete_clique : ∀ d ∈ ({13,14,15} : Finset (Fin 16)),
    ∀ a b : Fin 5, a ≠ 4 → b ≠ 4 → a ≠ b →
    (akDiagram d).1 (upperIndex a b) = true ∧
    (akDiagram d).2 (upperIndex a b) = true := by decide +kernel

theorem d14_d16_subsequence_fourProducts_zero
    {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : AdmissibleMasses mass)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero)
    {d : Fin 16} (hd : l.diagramCode = akDiagram d)
    (hk : d ∈ ({13,14,15} : Finset (Fin 16))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ e : Fin 10, Tendsto (fun t => (q (φ t)).fiveBodyFourProduct e) atTop (𝓝 0) := by
  obtain ⟨φ, hφ, ⟨o⟩⟩ := exists_sequenceOrderAssignment q hb 0 1 (by decide) ha
  let r : OrderedDiagramRealization mass l.diagramCode := {
    sequence := q ∘ φ
    balanced := fun t => hb (φ t)
    anchor₁ := 0
    anchor₂ := 1
    anchors_distinct := by decide
    vanishing := ha.comp hφ.tendsto_atTop
    leading := l.comp φ hφ.tendsto_atTop
    z_nonzero := hz
    w_nonzero := hw
    diagram_eq := rfl
    orders := o
  }
  refine ⟨φ, hφ, fun e => r.four_product_tendsto_zero_of_four_body_clique hm 4 0 (by decide) ?_ e⟩
  intro a b ha hb hab
  have hs := d14_d16_complete_clique d hk a b ha hb hab
  have hc : r.leading.diagramCode = akDiagram d := r.diagram_eq.trans hd
  exact ⟨r.leading.z_force_ne_zero_of_code hc a b hab hs.1,
    r.leading.w_force_ne_zero_of_code hc a b hab hs.2⟩

theorem d14_d16_not_escaping
    {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : AdmissibleMasses mass)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero)
    {d : Fin 16} (hd : l.diagramCode = akDiagram d)
    (hk : d ∈ ({13,14,15} : Finset (Fin 16))) :
    ¬ FourProductEscapes q := by
  rintro ⟨e, he⟩
  obtain ⟨φ,hφ,hzero⟩ := d14_d16_subsequence_fourProducts_zero l hm hb ha hz hw hd hk
  exact not_tendsto_atTop_of_tendsto_nhds (hzero e).norm (he.comp hφ.tendsto_atTop)

end
end CentralConfigurations.FiveBody.Ordinary
