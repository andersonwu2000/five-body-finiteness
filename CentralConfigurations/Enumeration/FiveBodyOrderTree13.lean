import CentralConfigurations.Enumeration.OrderRefutationTrees
import CentralConfigurations.Enumeration.FiveBodySourceData

/-!
# Exhaustive checked order refutation of source diagram 13

Generated from an untrusted search tree. All admitted branch values are
covered by proof terms; each update and obstruction is kernel-reduced.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CentralConfigurations.FiveBodyOrderTreeCertificates

open scoped Topology
open Filter

def d13n1Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 2, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]

def d13n1Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[3, 2, 8, 8, 4, 3, 8, 8, 4, 8, 8, 8, 8, 8, 4, 32, 32, 32, 32, 32, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]

def d13n1Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.separation 0 0 1 4)), #[15, 2, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.estimate 0 1)), #[15, 2, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.estimate 1 4)), #[15, 2, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 48, 48, 48, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 1 4)), #[15, 2, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 48, 48, 32, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 2 4)), #[15, 2, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 32, 48, 32, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 3 4)), #[15, 2, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 32, 32, 32, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 2 4)), #[15, 2, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 32, 32, 32, 32, 16, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 3 4)), #[15, 2, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 32, 32, 32, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    (.close 0 1 0 1, #[3, 2, 8, 8, 4, 3, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 32, 32, 32, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 2)), #[3, 2, 8, 8, 4, 3, 8, 8, 4, 8, 8, 8, 15, 8, 15, 32, 32, 32, 32, 32, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 3)), #[3, 2, 8, 8, 4, 3, 8, 8, 4, 8, 8, 8, 8, 8, 15, 32, 32, 32, 32, 32, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 4)), #[3, 2, 8, 8, 4, 3, 8, 8, 4, 8, 8, 8, 8, 8, 4, 32, 32, 32, 32, 32, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32])
  ]

theorem d13n1_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 12) d13n1Input d13n1Trace d13n1Final = true := by
  decide +kernel

theorem d13n1_refuted : OrderRefutation (fiveBodySourceDiagram 12) d13n1Input := by
  apply OrderRefutation.trace _ d13n1Final d13n1Trace d13n1_trace_checked
  exact OrderRefutation.leaf _ (.row 0 1) (by decide +kernel)

def d13n3Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 16, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]

def d13n3Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 16, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]

def d13n3Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.estimate 1 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 16, 48, 48, 48, 32, 48, 48, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 1 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 16, 48, 48, 32, 32, 48, 48, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 2 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 16, 32, 48, 32, 32, 48, 48, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 3 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 16, 32, 32, 32, 32, 48, 48, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 2 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 16, 32, 32, 32, 32, 32, 48, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 3 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 16, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32])
  ]

theorem d13n3_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 12) d13n3Input d13n3Trace d13n3Final = true := by
  decide +kernel

theorem d13n3_refuted : OrderRefutation (fiveBodySourceDiagram 12) d13n3Input := by
  apply OrderRefutation.trace _ d13n3Final d13n3Trace d13n3_trace_checked
  exact OrderRefutation.leaf _ (.pair 0 0 1) (by decide +kernel)

def d13n4Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 16, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]

def d13n4Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 0, 16, 16, 16, 16, 0, 16, 16, 16, 0, 8, 8, 0, 8, 0]

def d13n4Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.estimate 1 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 16, 48, 48, 48, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 1 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 16, 48, 48, 16, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 2 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 16, 16, 48, 16, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 3 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 16, 16, 16, 16, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 2 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 16, 16, 16, 16, 32, 16, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 3 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 16, 16, 16, 16, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    (.center 1 0, #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 0, 16, 16, 16, 16, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    (.center 1 1, #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 0, 16, 16, 16, 16, 0, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    (.center 1 2, #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 0, 16, 16, 16, 16, 0, 16, 16, 16, 0, 8, 8, 32, 8, 32]),
    (.center 1 3, #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 0, 16, 16, 16, 16, 0, 16, 16, 16, 0, 8, 8, 0, 8, 32]),
    (.center 1 4, #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 0, 16, 16, 16, 16, 0, 16, 16, 16, 0, 8, 8, 0, 8, 0])
  ]

theorem d13n4_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 12) d13n4Input d13n4Trace d13n4Final = true := by
  decide +kernel

theorem d13n4_refuted : OrderRefutation (fiveBodySourceDiagram 12) d13n4Input := by
  apply OrderRefutation.trace _ d13n4Final d13n4Trace d13n4_trace_checked
  exact OrderRefutation.leaf _ (.empty (zwOrderSlot 1 0 0)) (by decide +kernel)

def d13n2Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]

def d13n2Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 16, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]

def d13n2Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.estimate 0 1)), #[15, 4, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 16, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32])
  ]

theorem d13n2_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 12) d13n2Input d13n2Trace d13n2Final = true := by
  decide +kernel

theorem d13n2_refuted : OrderRefutation (fiveBodySourceDiagram 12) d13n2Input := by
  apply OrderRefutation.trace _ d13n2Final d13n2Trace d13n2_trace_checked
  apply OrderRefutation.branch _ (zwOrderSlot 0 1 4)
  intro a ha
  have domain : d13n2Final (zwOrderSlot 0 1 4) = {1, 2} := by decide +kernel
  rw [domain] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · have he : Function.update d13n2Final (zwOrderSlot 0 1 4) {1} = d13n3Input := by decide +kernel
    rw [he]
    exact d13n3_refuted
  · have he : Function.update d13n2Final (zwOrderSlot 0 1 4) {2} = d13n4Input := by decide +kernel
    rw [he]
    exact d13n4_refuted

def d13n0Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[31, 6, 60, 60, 60, 31, 60, 60, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]

def d13n0Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 6, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]

def d13n0Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.position 0 0 2)), #[31, 6, 28, 60, 60, 31, 60, 60, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 3)), #[31, 6, 28, 28, 60, 31, 60, 60, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 4)), #[31, 6, 28, 28, 28, 31, 60, 60, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 1 2)), #[31, 6, 28, 28, 28, 31, 28, 60, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 1 3)), #[31, 6, 28, 28, 28, 31, 28, 28, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 0 0 1 4)), #[31, 6, 28, 28, 4, 31, 28, 28, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 0 0 2 4)), #[31, 6, 8, 28, 4, 31, 28, 28, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 0 0 3 4)), #[31, 6, 8, 8, 4, 31, 28, 28, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 0 1 2 4)), #[31, 6, 8, 8, 4, 31, 8, 28, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 2 4)), #[31, 6, 8, 8, 4, 31, 8, 28, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 48, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 0 1 3 4)), #[31, 6, 8, 8, 4, 31, 8, 8, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 48, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 3 4)), #[31, 6, 8, 8, 4, 31, 8, 8, 6, 31, 8, 8, 31, 8, 31, 32, 48, 60, 60, 60, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.estimate 0 2)), #[31, 6, 8, 8, 4, 31, 8, 8, 6, 31, 8, 8, 31, 8, 31, 32, 48, 48, 60, 60, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.estimate 0 3)), #[31, 6, 8, 8, 4, 31, 8, 8, 6, 31, 8, 8, 31, 8, 31, 32, 48, 48, 48, 60, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.estimate 0 4)), #[31, 6, 8, 8, 4, 31, 8, 8, 6, 31, 8, 8, 31, 8, 31, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    (.center 0 0, #[15, 6, 8, 8, 4, 31, 8, 8, 6, 31, 8, 8, 31, 8, 31, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    (.center 0 1, #[15, 6, 8, 8, 4, 15, 8, 8, 6, 31, 8, 8, 31, 8, 31, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    (.center 0 2, #[15, 6, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 31, 8, 31, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    (.center 0 3, #[15, 6, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 15, 8, 31, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    (.center 0 4, #[15, 6, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32])
  ]

theorem d13n0_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 12) d13n0Input d13n0Trace d13n0Final = true := by
  decide +kernel

theorem d13n0_refuted : OrderRefutation (fiveBodySourceDiagram 12) d13n0Input := by
  apply OrderRefutation.trace _ d13n0Final d13n0Trace d13n0_trace_checked
  apply OrderRefutation.branch _ (zwOrderSlot 0 0 1)
  intro a ha
  have domain : d13n0Final (zwOrderSlot 0 0 1) = {1, 2} := by decide +kernel
  rw [domain] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · have he : Function.update d13n0Final (zwOrderSlot 0 0 1) {1} = d13n1Input := by decide +kernel
    rw [he]
    exact d13n1_refuted
  · have he : Function.update d13n0Final (zwOrderSlot 0 0 1) {2} = d13n2Input := by decide +kernel
    rw [he]
    exact d13n2_refuted

theorem diagram13_refuted : OrderRefutation (fiveBodySourceDiagram 12) (initialOrderBox (fiveBodySourceDiagram 12)) := by
  have he : initialOrderBox (fiveBodySourceDiagram 12) = d13n0Input := by decide +kernel
  rw [he]
  exact d13n0_refuted

theorem diagram13_impossible {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass)
    (i₀ j₀ : Fin 5) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : AdmissibleMasses mass)
    (hd : l.diagramCode = (fiveBodySourceDiagram 12)) : False :=
  impossible_of_orderRefutation q i₀ j₀ hij₀ ha hb l hm _ hd diagram13_refuted

end CentralConfigurations.FiveBodyOrderTreeCertificates
