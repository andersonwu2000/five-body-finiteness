import CentralConfigurations.Enumeration.OrderRefinementCertificates
import CentralConfigurations.Enumeration.AppendixMaximalEdgeSweep
import CentralConfigurations.Enumeration.AppendixRemoteBodyOrderDomains

/-!
# All certified update kinds used by the concrete order search

The basic triangle/Estimate operations are extended with the source's global
mass-center filter, close-pair and remote-body filters, and maximal-edge
initialization. Every recorded transition is checked on the complete box.
-/

namespace CentralConfigurations

open scoped Topology BigOperators
open Filter

inductive SourceOrderOp (n : ℕ) where
  | basic (op : OrderRefinementOp n)
  | center (color : Fin 2) (i : Fin n)
  | close (color other : Fin 2) (i j : Fin n)
  | remote (i : Fin n)
  | maximal
  deriving DecidableEq, Repr

def SourceOrderOp.apply {n : ℕ} (op : SourceOrderOp n) (d : DiagramCode n)
    (B : OrderBox (ZWOrderIndex n)) : OrderBox (ZWOrderIndex n) :=
  match op with
  | .basic op => op.apply d B
  | .center c i => centerOfMassAt true B c i
  | .close c other i j => closePairRefine B c other i j
  | .remote i => appendixRemoteBodyRefine d B i
  | .maximal => appendixMaximalEdgesSweep (BinaryMatrixCode.decode d.1) (BinaryMatrixCode.decode d.2) B

abbrev SourceOrderRecord (n : ℕ) := SourceOrderOp n × Array ℕ

def sourceOrderTraceCheck {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n))
    (steps : List (SourceOrderRecord n)) (target : OrderBox (ZWOrderIndex n)) : Bool :=
  match steps with
  | [] => decide (B = target)
  | (op, data) :: rest =>
      decide (op.apply d B = codedOrderBox n data) &&
        sourceOrderTraceCheck d (codedOrderBox n data) rest target

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass)
include hb hm

theorem admitted_sourceOrderOp (op : SourceOrderOp n)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    (op.apply l.diagramCode B).Admits o.orderCode := by
  have hM : (∑ j, mass j) ≠ 0 := hm Finset.univ ⟨i₀, Finset.mem_univ _⟩
  have hm' (j) : mass j ≠ 0 := by simpa using hm {j} (Finset.singleton_nonempty j)
  cases op with
  | basic op => exact o.admitted_orderRefinementOp l hb op B hB
  | center c i => exact o.admitted_centerOfMassAt hM B hB true c i
  | close c other i j => exact o.admitted_closePairRefine B hB c other i j (hm' j) hM
  | remote i => exact o.admitted_appendixRemoteBodyRefine hb l B hB i
  | maximal =>
      simpa only [SourceOrderOp.apply, ScaledZWLimit.diagramCode,
        BinaryMatrixCode.decode_encode _ l.z.matrix_binary l.z.matrix_symm,
        BinaryMatrixCode.decode_encode _ l.w.matrix_binary l.w.matrix_symm] using
          o.admitted_appendixMaximalEdgesSweep l hb hm B hB

theorem admitted_sourceOrderTrace (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (steps : List (SourceOrderRecord n))
    (target : OrderBox (ZWOrderIndex n))
    (hcheck : sourceOrderTraceCheck l.diagramCode B steps target = true) :
    target.Admits o.orderCode := by
  induction steps generalizing B with
  | nil => exact (of_decide_eq_true hcheck) ▸ hB
  | cons step steps ih =>
      simp only [sourceOrderTraceCheck, Bool.and_eq_true] at hcheck
      rcases hcheck with ⟨he, hr⟩
      have hnext := o.admitted_sourceOrderOp l hb hm step.1 B hB
      rw [of_decide_eq_true he] at hnext
      exact ih _ hnext hr

end SequenceOrderAssignment

end CentralConfigurations
