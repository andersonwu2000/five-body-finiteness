import CentralConfigurations.Enumeration.AppendixTriangleRefinement
import CentralConfigurations.Enumeration.EqualTriangleOrders
import CentralConfigurations.Enumeration.EstimateOrderDomains
import CentralConfigurations.Enumeration.PathMaximalFilter
import CentralConfigurations.Enumeration.BitMasks

/-!
# Replayable finite order-refinement certificates

The search procedure is untrusted. A certificate records a finite sequence
of source updates and their resulting boxes. The kernel checks each equality,
and the soundness theorem transports the actual order assignment through it.
No completeness, termination, or correctness assumption about the producer
is used. A failed two-row distance condition supplies the final contradiction.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

def orderDiagramEdge {n : ℕ} (d : DiagramCode n) (i j : Fin n) : Bool :=
  d.1 (upperIndex i j) || d.2 (upperIndex i j)

def checkedEqualTriangle {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i j k : Fin n) : OrderBox (ZWOrderIndex n) :=
  if i ≠ j ∧ j ≠ k ∧ i ≠ k ∧ orderDiagramEdge d i j = true ∧
      orderDiagramEdge d j k = true ∧ orderDiagramEdge d i k = true then
    OrderBox.equalizeTriple B (zwOrderSlot color i j)
      (zwOrderSlot color j k) (zwOrderSlot color i k) else B

inductive OrderRefinementOp (n : ℕ) where
  | position (color : Fin 2) (i j : Fin n)
  | separation (color : Fin 2) (i j k : Fin n)
  | equal (color : Fin 2) (i j k : Fin n)
  | estimate (i j : Fin n)
  deriving DecidableEq, Repr

def OrderRefinementOp.apply {n : ℕ} (op : OrderRefinementOp n)
    (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n)) : OrderBox (ZWOrderIndex n) :=
  match op with
  | .position c i j => appendixPositionTriangle B c i j
  | .separation c i j k => appendixSeparationTriangle B c i j k
  | .equal c i j k => checkedEqualTriangle d B c i j k
  | .estimate i j => if h : i < j then estimateDiagramPair d B ⟨(i, j), h⟩ else B

/-- Row-major upper-triangular storage, with one natural-number bit mask per
domain. Missing array entries denote empty domains and cannot hide a branch. -/
def codedOrderBox (n : ℕ) (data : Array ℕ) : OrderBox (ZWOrderIndex n) :=
  fun p => Finset.univ.filter fun a =>
    (data.getD (p.1.val * (n * (n + 1) / 2) + BinaryMatrixCode.rowMajorBitIndex p.2) 0).testBit a.val

abbrev OrderRefinementRecord (n : ℕ) := OrderRefinementOp n × Array ℕ

def checkedOrderTrace {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n))
    (steps : List (OrderRefinementRecord n)) (target : OrderBox (ZWOrderIndex n)) : Bool :=
  match steps with
  | [] => decide (B = target)
  | (op, data) :: rest =>
      decide (op.apply d B = codedOrderBox n data) &&
        checkedOrderTrace d (codedOrderBox n data) rest target

def pairOrderObstruction {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i j : Fin n) : Bool :=
  let M := if color = 0 then sourceMaxOrderZ d B else sourceMaxOrderW d B
  decide (i < j ∧ M i = {i, j} ∧ M j = {i, j} ∧
    (3 : Fin 6) ∉ radiusDomainEntry (producedDistanceBox d B) i j)

namespace ScaledZWLimit

theorem force_or_of_orderDiagramEdge {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (i j : Fin n) (hij : i ≠ j) (h : orderDiagramEdge l.diagramCode i j = true) :
    l.z.force i j ≠ 0 ∨ l.w.force i j ≠ 0 := by
  classical
  simp only [orderDiagramEdge, Bool.or_eq_true] at h
  rcases h with hz | hw
  · left
    simpa [l.diagramCode_z_entry, OneColorLimit.Incident, hij] using hz
  · right
    simpa [l.diagramCode_w_entry, OneColorLimit.Incident, hij] using hw

end ScaledZWLimit

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem admitted_checkedEqualTriangle (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color : Fin 2) (i j k : Fin n) :
    (checkedEqualTriangle l.diagramCode B color i j k).Admits o.orderCode := by
  unfold checkedEqualTriangle
  split_ifs with h
  · exact o.admitted_equalizeTriangle l hb B hB color i j k h.1 h.2.1 h.2.2.1
      (l.force_or_of_orderDiagramEdge i j h.1 h.2.2.2.1)
      (l.force_or_of_orderDiagramEdge j k h.2.1 h.2.2.2.2.1)
      (l.force_or_of_orderDiagramEdge i k h.2.2.1 h.2.2.2.2.2)
  · exact hB

theorem admitted_orderRefinementOp (op : OrderRefinementOp n)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    (op.apply l.diagramCode B).Admits o.orderCode := by
  cases op with
  | position c i j => exact o.admitted_appendixPositionTriangle B hB c i j
  | separation c i j k => exact o.admitted_appendixSeparationTriangle B hB c i j k
  | equal c i j k => exact o.admitted_checkedEqualTriangle l hb B hB c i j k
  | estimate i j =>
      simp only [OrderRefinementOp.apply]
      split_ifs with hij
      · exact o.admitted_estimateDiagramPair l hb B hB ⟨(i, j), hij⟩
      · exact hB

theorem admitted_checkedOrderTrace (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (steps : List (OrderRefinementRecord n))
    (target : OrderBox (ZWOrderIndex n))
    (hcheck : checkedOrderTrace l.diagramCode B steps target = true) :
    target.Admits o.orderCode := by
  induction steps generalizing B with
  | nil => exact (of_decide_eq_true hcheck) ▸ hB
  | cons step steps ih =>
      simp only [checkedOrderTrace, Bool.and_eq_true] at hcheck
      rcases hcheck with ⟨he, hr⟩
      have hnext := o.admitted_orderRefinementOp l hb step.1 B hB
      rw [of_decide_eq_true he] at hnext
      exact ih _ hnext hr

theorem pairOrderObstruction_eq_false (hm : AdmissibleMasses mass)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode)
    (color : Fin 2) (i j : Fin n) : pairOrderObstruction l.diagramCode B color i j = false := by
  have h := of_decide_eq_true (o.source_maximalPairDistanceCheck l hb B hB hm)
  unfold pairOrderObstruction
  apply decide_eq_false
  intro hn
  rcases hn with ⟨hij, hi, hj, hr⟩
  by_cases hc : color = 0
  · simp only [if_pos hc] at hi hj
    exact hr ((h i j hij).1 hi hj)
  · simp only [if_neg hc] at hi hj
    exact hr ((h i j hij).2 hi hj)

end SequenceOrderAssignment

/-- An initial-box trace and a checked pair obstruction exclude the actual
balanced singular limit. No fixed order assignment is assumed at entry. -/
theorem impossible_of_checkedOrderTrace {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : AdmissibleMasses mass)
    (d : DiagramCode n) (hd : l.diagramCode = d)
    (steps : List (OrderRefinementRecord n)) (target : OrderBox (ZWOrderIndex n))
    (hcheck : checkedOrderTrace d (initialOrderBox d) steps target = true)
    (color : Fin 2) (i j : Fin n) (hreject : pairOrderObstruction d target color i j = true) :
    False := by
  obtain ⟨φ, hφ, ⟨o⟩⟩ := exists_sequenceOrderAssignment q hb i₀ j₀ hij₀ ha
  let l' := l.comp φ hφ.tendsto_atTop
  have hd' : l'.diagramCode = d := hd
  have hc : checkedOrderTrace l'.diagramCode (initialOrderBox l'.diagramCode) steps target = true := by
    simpa only [hd'] using hcheck
  have hB := o.admitted_checkedOrderTrace l' (fun t => hb (φ t)) _
    (o.admitted_initialOrderBox l' (fun t => hb (φ t))) steps target hc
  have hn := o.pairOrderObstruction_eq_false l' (fun t => hb (φ t)) hm target hB color i j
  change pairOrderObstruction l.diagramCode target color i j = false at hn
  rw [hd, hreject] at hn
  contradiction

end CentralConfigurations
