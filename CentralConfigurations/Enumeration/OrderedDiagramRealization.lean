import CentralConfigurations.Enumeration.DistanceOrderDomains

/-!
# Actual ordered realizations of canonical diagram labels

An orbit representative is realized by relabeling the actual solutions and
their masses, with an optional global color exchange. A further common
extraction supplies all levels while preserving that exact diagram. No
invariance of an order-filter implementation is assumed.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

structure OrderedDiagramRealization {n : ℕ} (mass : Fin n → ℂ) (d : DiagramCode n) where
  sequence : ℕ → ZWSystem ℂ n mass
  balanced : ∀ t, ‖(sequence t).zVector‖ = ‖(sequence t).wVector‖
  anchor₁ : Fin n
  anchor₂ : Fin n
  anchors_distinct : anchor₁ ≠ anchor₂
  vanishing : Tendsto (fun t => (sequence t).inverseScale) atTop (𝓝 0)
  leading : ScaledZWLimit sequence (fun t => (sequence t).inverseScale)
  z_nonzero : leading.z.Nonzero
  w_nonzero : leading.w.Nonzero
  diagram_eq : leading.diagramCode = d
  orders : SequenceOrderAssignment sequence anchor₁ anchor₂ anchors_distinct vanishing

theorem exists_ordered_diagram_realization {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j : Fin n) (hij : i ≠ j)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) :
    Nonempty (OrderedDiagramRealization mass l.diagramCode) := by
  obtain ⟨φ, hφ, ⟨o⟩⟩ := exists_sequenceOrderAssignment q hb i j hij ha
  exact ⟨{
    sequence := q ∘ φ
    balanced := fun t => hb (φ t)
    anchor₁ := i
    anchor₂ := j
    anchors_distinct := hij
    vanishing := ha.comp hφ.tendsto_atTop
    leading := l.comp φ hφ.tendsto_atTop
    z_nonzero := hz
    w_nonzero := hw
    diagram_eq := rfl
    orders := o
  }⟩

/-- Every representative of the actual diagram orbit has an ordered realization
with the same permutation applied to the masses. -/
theorem ordered_realization_of_mem_orbit {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j : Fin n) (hij : i ≠ j)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero)
    {d : DiagramCode n} (hd : d ∈ DiagramCode.orbit l.diagramCode) :
    ∃ e : Equiv.Perm (Fin n), Nonempty (OrderedDiagramRealization (fun k => mass (e k)) d) := by
  obtain ⟨e, flip, hcode⟩ := (DiagramCode.mem_orbit_iff _ _).mp hd
  let qr := fun t => (q t).relabel e
  let lr := l.relabelCanonical e
  have hbr : ∀ t, ‖(qr t).zVector‖ = ‖(qr t).wVector‖ := by
    simpa only [qr, ZWSystem.zVector_norm_relabel, ZWSystem.wVector_norm_relabel] using hb
  have har : Tendsto (fun t => (qr t).inverseScale) atTop (𝓝 0) := by
    simpa only [qr, ZWSystem.inverseScale_relabel] using ha
  have hijr : e.symm i ≠ e.symm j := fun h => hij (e.symm.injective h)
  have hzr : lr.z.Nonzero := (l.z.nonzero_relabel_iff e).mpr hz
  have hwr : lr.w.Nonzero := (l.w.nonzero_relabel_iff e).mpr hw
  refine ⟨e, ?_⟩
  cases flip
  · have hdiagram : lr.diagramCode = d := by
      rw [show lr.diagramCode = DiagramCode.relabel l.diagramCode e from
        l.diagramCode_relabelCanonical e]
      simpa only [DiagramCode.transform, Bool.false_eq_true, if_false] using hcode
    simpa only [hdiagram] using exists_ordered_diagram_realization qr hbr
      (e.symm i) (e.symm j) hijr har lr hzr hwr
  · have has : Tendsto (fun t => ((qr t).swap).inverseScale) atTop (𝓝 0) := by
      change Tendsto (fun t => (‖(qr t).wVector‖ : ℂ)⁻¹) atTop (𝓝 0)
      simpa only [ZWSystem.inverseScale, ← hbr] using har
    have hdiagram : (lr.swapBalanced hbr).diagramCode = d := by
      change DiagramCode.swap (l.relabelCanonical e).diagramCode = d
      rw [l.diagramCode_relabelCanonical e]
      simpa only [DiagramCode.transform, if_true] using hcode
    simpa only [hdiagram] using exists_ordered_diagram_realization
      (fun t => (qr t).swap) (fun t => (hbr t).symm)
      (e.symm i) (e.symm j) hijr has (lr.swapBalanced hbr) hwr hzr

namespace OrderedDiagramRealization

variable {n : ℕ} {mass : Fin n → ℂ} {d : DiagramCode n}
variable (r : OrderedDiagramRealization mass d)

theorem initialCoverage :
    ZWOrderCoverage r.sequence r.anchor₁ r.anchor₂ r.anchors_distinct r.vanishing
      {initialOrderBox d} := by
  simpa only [r.diagram_eq] using initialOrderBox_covers_sequence r.sequence
    r.anchor₁ r.anchor₂ r.anchors_distinct r.vanishing r.balanced r.leading

theorem initialDistanceCoverage :
    ROrderCoverage r.sequence r.anchor₁ r.anchor₂ r.anchors_distinct r.vanishing
      (producedDistanceFamily d {initialOrderBox d}) := by
  simpa only [r.diagram_eq] using r.initialCoverage.producedDistances r.leading r.balanced

theorem admitted_initial : (initialOrderBox d).Admits r.orders.orderCode := by
  simpa only [r.diagram_eq] using r.orders.admitted_initialOrderBox r.leading r.balanced

theorem admitted_initial_distances :
    (producedDistanceBox d (initialOrderBox d)).Admits r.orders.radiusCode := by
  simpa only [r.diagram_eq] using
    r.orders.admitted_producedDistanceBox r.leading r.balanced (initialOrderBox d) r.admitted_initial

end OrderedDiagramRealization

end CentralConfigurations
