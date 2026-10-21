import CentralConfigurations.Enumeration.OrderRefutationTrees
import CentralConfigurations.Enumeration.FiveBodySourceData

/-!
# Exhaustive checked order refutation of source diagram 11

Generated from an untrusted search tree. All admitted branch values are
covered by proof terms; each update and obstruction is kernel-reduced.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CentralConfigurations.FiveBodyOrderTreeCertificates

open scoped Topology
open Filter

def d11n1Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 2, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]

def d11n1Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[3, 4, 8, 8, 2, 4, 8, 8, 4, 8, 8, 8, 8, 8, 3, 32, 32, 32, 32, 32, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]

def d11n1Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.separation 0 0 1 4)), #[15, 4, 8, 8, 2, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.estimate 0 4)), #[15, 4, 8, 8, 2, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 32, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.estimate 1 4)), #[15, 4, 8, 8, 2, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 32, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 1 4)), #[15, 4, 8, 8, 2, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 48, 48, 32, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 2 4)), #[15, 4, 8, 8, 2, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 32, 48, 32, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 3 4)), #[15, 4, 8, 8, 2, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 32, 32, 32, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 2 4)), #[15, 4, 8, 8, 2, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 32, 32, 32, 32, 16, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 3 4)), #[15, 4, 8, 8, 2, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 32, 32, 32, 32, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    (.close 0 1 0 4, #[3, 4, 8, 8, 2, 15, 8, 8, 4, 15, 8, 8, 15, 8, 3, 32, 32, 32, 32, 32, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 1)), #[3, 4, 8, 8, 2, 4, 8, 8, 4, 15, 8, 8, 15, 8, 3, 32, 32, 32, 32, 32, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 2)), #[3, 4, 8, 8, 2, 4, 8, 8, 4, 8, 8, 8, 15, 8, 3, 32, 32, 32, 32, 32, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 3)), #[3, 4, 8, 8, 2, 4, 8, 8, 4, 8, 8, 8, 8, 8, 3, 32, 32, 32, 32, 32, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32])
  ]

theorem d11n1_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 10) d11n1Input d11n1Trace d11n1Final = true := by
  decide +kernel

theorem d11n1_refuted : OrderRefutation (fiveBodySourceDiagram 10) d11n1Input := by
  apply OrderRefutation.trace _ d11n1Final d11n1Trace d11n1_trace_checked
  exact OrderRefutation.leaf _ (.row 0 1) (by decide +kernel)

def d11n3Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 48, 16, 16, 16, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]

def d11n3Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[4, 4, 8, 8, 4, 3, 8, 8, 2, 8, 8, 8, 8, 8, 3, 32, 32, 16, 16, 16, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]

def d11n3Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.estimate 1 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 48, 16, 16, 16, 32, 48, 48, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 1 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 32, 16, 16, 16, 32, 48, 48, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 2 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 32, 16, 16, 16, 32, 32, 48, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 3 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 2, 15, 8, 8, 15, 8, 15, 32, 32, 16, 16, 16, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    (.close 0 1 1 4, #[15, 4, 8, 8, 4, 3, 8, 8, 2, 15, 8, 8, 15, 8, 3, 32, 32, 16, 16, 16, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 1)), #[4, 4, 8, 8, 4, 3, 8, 8, 2, 15, 8, 8, 15, 8, 3, 32, 32, 16, 16, 16, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 2)), #[4, 4, 8, 8, 4, 3, 8, 8, 2, 8, 8, 8, 15, 8, 3, 32, 32, 16, 16, 16, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 3)), #[4, 4, 8, 8, 4, 3, 8, 8, 2, 8, 8, 8, 8, 8, 3, 32, 32, 16, 16, 16, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32])
  ]

theorem d11n3_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 10) d11n3Input d11n3Trace d11n3Final = true := by
  decide +kernel

theorem d11n3_refuted : OrderRefutation (fiveBodySourceDiagram 10) d11n3Input := by
  apply OrderRefutation.trace _ d11n3Final d11n3Trace d11n3_trace_checked
  exact OrderRefutation.leaf _ (.row 0 0) (by decide +kernel)

def d11n4Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 48, 16, 16, 16, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]

def d11n4Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 0, 16, 16, 16, 16, 0, 16, 16, 16, 0, 8, 8, 0, 8, 0]

def d11n4Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.estimate 1 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 48, 16, 16, 16, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 1 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 16, 16, 16, 16, 32, 48, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 2 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 16, 16, 16, 16, 32, 16, 48, 16, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 3 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 32, 16, 16, 16, 16, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    (.center 1 0, #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 0, 16, 16, 16, 16, 32, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    (.center 1 1, #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 0, 16, 16, 16, 16, 0, 16, 16, 16, 32, 8, 8, 32, 8, 32]),
    (.center 1 2, #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 0, 16, 16, 16, 16, 0, 16, 16, 16, 0, 8, 8, 32, 8, 32]),
    (.center 1 3, #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 0, 16, 16, 16, 16, 0, 16, 16, 16, 0, 8, 8, 0, 8, 32]),
    (.center 1 4, #[15, 4, 8, 8, 4, 15, 8, 8, 4, 15, 8, 8, 15, 8, 15, 0, 16, 16, 16, 16, 0, 16, 16, 16, 0, 8, 8, 0, 8, 0])
  ]

theorem d11n4_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 10) d11n4Input d11n4Trace d11n4Final = true := by
  decide +kernel

theorem d11n4_refuted : OrderRefutation (fiveBodySourceDiagram 10) d11n4Input := by
  apply OrderRefutation.trace _ d11n4Final d11n4Trace d11n4_trace_checked
  exact OrderRefutation.leaf _ (.empty (zwOrderSlot 1 0 0)) (by decide +kernel)

def d11n2Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]

def d11n2Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 48, 16, 16, 16, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]

def d11n2Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.estimate 0 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 16, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 2 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 48, 16, 48, 16, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 3 4)), #[15, 4, 8, 8, 4, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 48, 16, 16, 16, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32])
  ]

theorem d11n2_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 10) d11n2Input d11n2Trace d11n2Final = true := by
  decide +kernel

theorem d11n2_refuted : OrderRefutation (fiveBodySourceDiagram 10) d11n2Input := by
  apply OrderRefutation.trace _ d11n2Final d11n2Trace d11n2_trace_checked
  apply OrderRefutation.branch _ (zwOrderSlot 0 1 4)
  intro a ha
  have domain : d11n2Final (zwOrderSlot 0 1 4) = {1, 2} := by decide +kernel
  rw [domain] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · have he : Function.update d11n2Final (zwOrderSlot 0 1 4) {1} = d11n3Input := by decide +kernel
    rw [he]
    exact d11n3_refuted
  · have he : Function.update d11n2Final (zwOrderSlot 0 1 4) {2} = d11n4Input := by decide +kernel
    rw [he]
    exact d11n4_refuted

def d11n0Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[31, 60, 60, 60, 6, 31, 60, 60, 6, 31, 8, 8, 31, 8, 31, 32, 60, 60, 60, 48, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]

def d11n0Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[15, 4, 8, 8, 6, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]

def d11n0Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.position 0 0 1)), #[31, 28, 60, 60, 6, 31, 60, 60, 6, 31, 8, 8, 31, 8, 31, 32, 60, 60, 60, 48, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 2)), #[31, 28, 28, 60, 6, 31, 60, 60, 6, 31, 8, 8, 31, 8, 31, 32, 60, 60, 60, 48, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 3)), #[31, 28, 28, 28, 6, 31, 60, 60, 6, 31, 8, 8, 31, 8, 31, 32, 60, 60, 60, 48, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 1 2)), #[31, 28, 28, 28, 6, 31, 28, 60, 6, 31, 8, 8, 31, 8, 31, 32, 60, 60, 60, 48, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 1 3)), #[31, 28, 28, 28, 6, 31, 28, 28, 6, 31, 8, 8, 31, 8, 31, 32, 60, 60, 60, 48, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 0 0 1 4)), #[31, 4, 28, 28, 6, 31, 28, 28, 6, 31, 8, 8, 31, 8, 31, 32, 60, 60, 60, 48, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 0 0 2 4)), #[31, 4, 8, 28, 6, 31, 28, 28, 6, 31, 8, 8, 31, 8, 31, 32, 60, 60, 60, 48, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 2 4)), #[31, 4, 8, 28, 6, 31, 28, 28, 6, 31, 8, 8, 31, 8, 31, 32, 60, 48, 60, 48, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 0 0 3 4)), #[31, 4, 8, 8, 6, 31, 28, 28, 6, 31, 8, 8, 31, 8, 31, 32, 60, 48, 60, 48, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 0 3 4)), #[31, 4, 8, 8, 6, 31, 28, 28, 6, 31, 8, 8, 31, 8, 31, 32, 60, 48, 48, 48, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 0 1 2 4)), #[31, 4, 8, 8, 6, 31, 8, 28, 6, 31, 8, 8, 31, 8, 31, 32, 60, 48, 48, 48, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 2 4)), #[31, 4, 8, 8, 6, 31, 8, 28, 6, 31, 8, 8, 31, 8, 31, 32, 60, 48, 48, 48, 32, 48, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 0 1 3 4)), #[31, 4, 8, 8, 6, 31, 8, 8, 6, 31, 8, 8, 31, 8, 31, 32, 60, 48, 48, 48, 32, 48, 60, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 3 4)), #[31, 4, 8, 8, 6, 31, 8, 8, 6, 31, 8, 8, 31, 8, 31, 32, 60, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    ((.basic (.estimate 0 1)), #[31, 4, 8, 8, 6, 31, 8, 8, 6, 31, 8, 8, 31, 8, 31, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    (.center 0 0, #[15, 4, 8, 8, 6, 31, 8, 8, 6, 31, 8, 8, 31, 8, 31, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    (.center 0 1, #[15, 4, 8, 8, 6, 15, 8, 8, 6, 31, 8, 8, 31, 8, 31, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    (.center 0 2, #[15, 4, 8, 8, 6, 15, 8, 8, 6, 15, 8, 8, 31, 8, 31, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    (.center 0 3, #[15, 4, 8, 8, 6, 15, 8, 8, 6, 15, 8, 8, 15, 8, 31, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32]),
    (.center 0 4, #[15, 4, 8, 8, 6, 15, 8, 8, 6, 15, 8, 8, 15, 8, 15, 32, 48, 48, 48, 48, 32, 48, 48, 48, 32, 8, 8, 32, 8, 32])
  ]

theorem d11n0_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 10) d11n0Input d11n0Trace d11n0Final = true := by
  decide +kernel

theorem d11n0_refuted : OrderRefutation (fiveBodySourceDiagram 10) d11n0Input := by
  apply OrderRefutation.trace _ d11n0Final d11n0Trace d11n0_trace_checked
  apply OrderRefutation.branch _ (zwOrderSlot 0 0 4)
  intro a ha
  have domain : d11n0Final (zwOrderSlot 0 0 4) = {1, 2} := by decide +kernel
  rw [domain] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · have he : Function.update d11n0Final (zwOrderSlot 0 0 4) {1} = d11n1Input := by decide +kernel
    rw [he]
    exact d11n1_refuted
  · have he : Function.update d11n0Final (zwOrderSlot 0 0 4) {2} = d11n2Input := by decide +kernel
    rw [he]
    exact d11n2_refuted

theorem diagram11_refuted : OrderRefutation (fiveBodySourceDiagram 10) (initialOrderBox (fiveBodySourceDiagram 10)) := by
  have he : initialOrderBox (fiveBodySourceDiagram 10) = d11n0Input := by decide +kernel
  rw [he]
  exact d11n0_refuted

theorem diagram11_impossible {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass)
    (i₀ j₀ : Fin 5) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : AdmissibleMasses mass)
    (hd : l.diagramCode = (fiveBodySourceDiagram 10)) : False :=
  impossible_of_orderRefutation q i₀ j₀ hij₀ ha hb l hm _ hd diagram11_refuted

end CentralConfigurations.FiveBodyOrderTreeCertificates
