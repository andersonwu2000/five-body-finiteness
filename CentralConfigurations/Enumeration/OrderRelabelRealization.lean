import CentralConfigurations.Enumeration.OrderRelabeling
import CentralConfigurations.Enumeration.OrderedDiagramRealization

/-! Relabel the actual sequence and its already fixed order assignment.
The same permutation acts on the masses, both colors, and all distance
levels. No new extraction or invariance assumption on the search is used. -/

namespace CentralConfigurations

open scoped Topology BigOperators
open Filter

theorem AdmissibleMasses.relabel {K : Type*} [AddCommMonoid K] {n : ℕ}
    {mass : Fin n → K} (hm : AdmissibleMasses mass) (e : Equiv.Perm (Fin n)) :
    AdmissibleMasses (fun i => mass (e i)) := by
  intro s hs
  have h := hm (s.image e) (hs.image e)
  simpa only [Finset.sum_image (fun i _ j _ h => e.injective h)] using h

theorem ZWSystem.zOrderValue_relabel {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (e : Equiv.Perm (Fin n)) (i j : Fin n) :
    (q.relabel e).zOrderValue i j = q.zOrderValue (e i) (e j) := by
  simp only [zOrderValue,relabel,e.injective.eq_iff]

theorem ZWSystem.wOrderValue_relabel {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (e : Equiv.Perm (Fin n)) (i j : Fin n) :
    (q.relabel e).wOrderValue i j = q.wOrderValue (e i) (e j) := by
  simp only [wOrderValue,relabel,e.injective.eq_iff]

theorem ZWSystem.radiusOrderValue_relabel {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (e : Equiv.Perm (Fin n)) (i j : Fin n) :
    (q.relabel e).radiusOrderValue i j = q.radiusOrderValue (e i) (e j) := rfl

theorem ZWSystem.vanishing_relabel {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass}
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) (e : Equiv.Perm (Fin n)) :
    Tendsto (fun t => ((q t).relabel e).inverseScale) atTop (𝓝 0) := by
  simpa only [inverseScale_relabel] using ha

namespace SequenceOrderAssignment
variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

def relabel (e : Equiv.Perm (Fin n)) :
    SequenceOrderAssignment (fun t => (q t).relabel e) (e.symm i₀) (e.symm j₀)
      (fun h => hij₀ (e.symm.injective h)) (ZWSystem.vanishing_relabel ha e) where
  z i j := o.z (e i) (e j)
  w i j := o.w (e i) (e j)
  radius i j := o.radius (e i) (e j)
  z_level i j := by
    simpa only [ZWSystem.zOrderValue_relabel,ZWSystem.orderPositionScales,ZWSystem.epsilon,
      ZWSystem.zVector_norm_relabel] using o.z_level (e i) (e j)
  w_level i j := by
    simpa only [ZWSystem.wOrderValue_relabel,ZWSystem.orderPositionScales,ZWSystem.epsilon,
      ZWSystem.zVector_norm_relabel] using o.w_level (e i) (e j)
  radius_level i j := by
    simpa only [ZWSystem.radiusOrderValue_relabel,ZWSystem.orderDistanceScales,ZWSystem.epsilon,
      ZWSystem.zVector_norm_relabel] using o.radius_level (e i) (e j)

theorem relabel_orderCode (e : Equiv.Perm (Fin n)) :
    (o.relabel e).orderCode = relabelZWOrder o.orderCode e := by
  funext p
  rcases p with ⟨c,p⟩
  fin_cases c
  · exact (symmetric_upperIndex o.z o.z_symm (e p.1.1) (e p.1.2)).symm
  · exact (symmetric_upperIndex o.w o.w_symm (e p.1.1) (e p.1.2)).symm

theorem admitted_relabelZWOrder (e : Equiv.Perm (Fin n))
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    OrderBox.Admits (relabelZWOrder B e) (o.relabel e).orderCode := by
  rw [o.relabel_orderCode]
  exact (relabelZWOrder_admits_iff B o.orderCode e).mpr hB

end SequenceOrderAssignment

namespace OrderedDiagramRealization
variable {n : ℕ} {mass : Fin n → ℂ} {d : DiagramCode n}
variable (r : OrderedDiagramRealization mass d)

def relabelAs (e : Equiv.Perm (Fin n)) (d' : DiagramCode n)
    (hd : DiagramCode.relabel d e = d') : OrderedDiagramRealization (fun i => mass (e i)) d' where
  sequence t := (r.sequence t).relabel e
  balanced t := by simpa only [ZWSystem.zVector_norm_relabel,ZWSystem.wVector_norm_relabel] using r.balanced t
  anchor₁ := e.symm r.anchor₁
  anchor₂ := e.symm r.anchor₂
  anchors_distinct := fun h => r.anchors_distinct (e.symm.injective h)
  vanishing := ZWSystem.vanishing_relabel r.vanishing e
  leading := r.leading.relabelCanonical e
  z_nonzero := (r.leading.z.nonzero_relabel_iff e).mpr r.z_nonzero
  w_nonzero := (r.leading.w.nonzero_relabel_iff e).mpr r.w_nonzero
  diagram_eq := by rw [r.leading.diagramCode_relabelCanonical,r.diagram_eq,hd]
  orders := r.orders.relabel e

theorem relabelAs_orderCode (e : Equiv.Perm (Fin n)) (d' : DiagramCode n)
    (hd : DiagramCode.relabel d e = d') :
    (r.relabelAs e d' hd).orders.orderCode = relabelZWOrder r.orders.orderCode e :=
  r.orders.relabel_orderCode e

end OrderedDiagramRealization
end CentralConfigurations
