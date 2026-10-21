import CentralConfigurations.Enumeration.OrderRefutationTrees
import CentralConfigurations.Enumeration.FiveBodySourceData

/-!
# Exhaustive checked order refutation of source diagram 17

Generated from an untrusted search tree. All admitted branch values are
covered by proof terms; each update and obstruction is kernel-reduced.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CentralConfigurations.FiveBodyOrderTreeCertificates

open scoped Topology
open Filter

def d17n1Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[31, 4, 2, 32, 32, 31, 6, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 48, 32, 32, 32, 48, 32, 32, 32, 32, 32, 3, 2, 3]

def d17n1Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[3, 4, 2, 32, 32, 4, 4, 32, 32, 3, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 16, 32, 32, 32, 32, 32, 3, 2, 3]

def d17n1Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.separation 0 0 1 2)), #[31, 4, 2, 32, 32, 31, 4, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 48, 32, 32, 32, 48, 32, 32, 32, 32, 32, 3, 2, 3]),
    ((.basic (.estimate 0 2)), #[31, 4, 2, 32, 32, 31, 4, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 32, 32, 32, 32, 48, 32, 32, 32, 32, 32, 3, 2, 3]),
    ((.basic (.estimate 1 2)), #[31, 4, 2, 32, 32, 31, 4, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 32, 32, 32, 32, 16, 32, 32, 32, 32, 32, 3, 2, 3]),
    ((.basic (.separation 1 0 1 2)), #[31, 4, 2, 32, 32, 31, 4, 32, 32, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 16, 32, 32, 32, 32, 32, 3, 2, 3]),
    (.close 0 1 0 2, #[3, 4, 2, 32, 32, 31, 4, 32, 32, 3, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 16, 32, 32, 32, 32, 32, 3, 2, 3]),
    ((.basic (.position 0 0 1)), #[3, 4, 2, 32, 32, 4, 4, 32, 32, 3, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 32, 16, 32, 32, 32, 32, 32, 3, 2, 3])
  ]

theorem d17n1_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 16) d17n1Input d17n1Trace d17n1Final = true := by
  decide +kernel

theorem d17n1_refuted : OrderRefutation (fiveBodySourceDiagram 16) d17n1Input := by
  apply OrderRefutation.trace _ d17n1Final d17n1Trace d17n1_trace_checked
  exact OrderRefutation.leaf _ (.shrinking) (by decide +kernel)

def d17n3Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[31, 4, 4, 32, 32, 31, 2, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 16, 32, 32, 32, 48, 32, 32, 32, 32, 32, 3, 2, 3]

def d17n3Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[4, 4, 4, 32, 32, 3, 2, 32, 32, 3, 32, 32, 32, 32, 32, 32, 32, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 3, 2, 3]

def d17n3Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.estimate 1 2)), #[31, 4, 4, 32, 32, 31, 2, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 3, 2, 3]),
    ((.basic (.separation 1 0 1 2)), #[31, 4, 4, 32, 32, 31, 2, 32, 32, 31, 32, 32, 32, 32, 32, 32, 32, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 3, 2, 3]),
    (.close 0 1 1 2, #[31, 4, 4, 32, 32, 3, 2, 32, 32, 3, 32, 32, 32, 32, 32, 32, 32, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 3, 2, 3]),
    ((.basic (.position 0 0 1)), #[4, 4, 4, 32, 32, 3, 2, 32, 32, 3, 32, 32, 32, 32, 32, 32, 32, 16, 32, 32, 32, 32, 32, 32, 32, 32, 32, 3, 2, 3])
  ]

theorem d17n3_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 16) d17n3Input d17n3Trace d17n3Final = true := by
  decide +kernel

theorem d17n3_refuted : OrderRefutation (fiveBodySourceDiagram 16) d17n3Input := by
  apply OrderRefutation.trace _ d17n3Final d17n3Trace d17n3_trace_checked
  exact OrderRefutation.leaf _ (.shrinking) (by decide +kernel)

def d17n4Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[31, 4, 4, 32, 32, 31, 4, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 16, 32, 32, 32, 48, 32, 32, 32, 32, 32, 3, 2, 3]

def d17n4Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[31, 4, 4, 32, 32, 31, 4, 32, 32, 31, 32, 32, 32, 32, 32, 32, 16, 16, 32, 32, 32, 16, 32, 32, 32, 32, 32, 3, 2, 3]

def d17n4Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.estimate 1 2)), #[31, 4, 4, 32, 32, 31, 4, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 16, 32, 32, 32, 16, 32, 32, 32, 32, 32, 3, 2, 3]),
    ((.basic (.separation 1 0 1 2)), #[31, 4, 4, 32, 32, 31, 4, 32, 32, 31, 32, 32, 32, 32, 32, 32, 16, 16, 32, 32, 32, 16, 32, 32, 32, 32, 32, 3, 2, 3])
  ]

theorem d17n4_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 16) d17n4Input d17n4Trace d17n4Final = true := by
  decide +kernel

theorem d17n4_refuted : OrderRefutation (fiveBodySourceDiagram 16) d17n4Input := by
  apply OrderRefutation.trace _ d17n4Final d17n4Trace d17n4_trace_checked
  exact OrderRefutation.leaf _ (.circle) (by decide +kernel)

def d17n2Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[31, 4, 4, 32, 32, 31, 6, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 48, 32, 32, 32, 48, 32, 32, 32, 32, 32, 3, 2, 3]

def d17n2Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[31, 4, 4, 32, 32, 31, 6, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 16, 32, 32, 32, 48, 32, 32, 32, 32, 32, 3, 2, 3]

def d17n2Trace : List (SourceOrderRecord 5) :=
  [
    ((.basic (.estimate 0 2)), #[31, 4, 4, 32, 32, 31, 6, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 16, 32, 32, 32, 48, 32, 32, 32, 32, 32, 3, 2, 3])
  ]

theorem d17n2_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 16) d17n2Input d17n2Trace d17n2Final = true := by
  decide +kernel

theorem d17n2_refuted : OrderRefutation (fiveBodySourceDiagram 16) d17n2Input := by
  apply OrderRefutation.trace _ d17n2Final d17n2Trace d17n2_trace_checked
  apply OrderRefutation.branch _ (zwOrderSlot 0 1 2)
  intro a ha
  have domain : d17n2Final (zwOrderSlot 0 1 2) = {1, 2} := by decide +kernel
  rw [domain] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · have he : Function.update d17n2Final (zwOrderSlot 0 1 2) {1} = d17n3Input := by decide +kernel
    rw [he]
    exact d17n3_refuted
  · have he : Function.update d17n2Final (zwOrderSlot 0 1 2) {2} = d17n4Input := by decide +kernel
    rw [he]
    exact d17n4_refuted

def d17n0Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[31, 60, 6, 60, 60, 31, 6, 60, 60, 31, 60, 60, 32, 48, 32, 32, 60, 48, 60, 60, 32, 48, 60, 60, 32, 60, 60, 31, 6, 31]

def d17n0Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[31, 4, 6, 32, 32, 31, 6, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 48, 32, 32, 32, 48, 32, 32, 32, 32, 32, 3, 2, 3]

def d17n0Trace : List (SourceOrderRecord 5) :=
  [
    (.maximal, #[31, 60, 6, 60, 60, 31, 6, 60, 60, 31, 60, 60, 32, 32, 32, 32, 60, 48, 60, 60, 32, 48, 60, 60, 32, 60, 60, 31, 2, 31]),
    ((.basic (.position 0 0 1)), #[31, 28, 6, 60, 60, 31, 6, 60, 60, 31, 60, 60, 32, 32, 32, 32, 60, 48, 60, 60, 32, 48, 60, 60, 32, 60, 60, 31, 2, 31]),
    ((.basic (.position 0 0 3)), #[31, 28, 6, 32, 60, 31, 6, 60, 60, 31, 60, 60, 32, 32, 32, 32, 60, 48, 60, 60, 32, 48, 60, 60, 32, 60, 60, 31, 2, 31]),
    ((.basic (.position 1 0 3)), #[31, 28, 6, 32, 60, 31, 6, 60, 60, 31, 60, 60, 32, 32, 32, 32, 60, 48, 32, 60, 32, 48, 60, 60, 32, 60, 60, 31, 2, 31]),
    ((.basic (.position 0 0 4)), #[31, 28, 6, 32, 32, 31, 6, 60, 60, 31, 60, 60, 32, 32, 32, 32, 60, 48, 32, 60, 32, 48, 60, 60, 32, 60, 60, 31, 2, 31]),
    ((.basic (.position 1 0 4)), #[31, 28, 6, 32, 32, 31, 6, 60, 60, 31, 60, 60, 32, 32, 32, 32, 60, 48, 32, 32, 32, 48, 60, 60, 32, 60, 60, 31, 2, 31]),
    ((.basic (.position 0 1 3)), #[31, 28, 6, 32, 32, 31, 6, 32, 60, 31, 60, 60, 32, 32, 32, 32, 60, 48, 32, 32, 32, 48, 60, 60, 32, 60, 60, 31, 2, 31]),
    ((.basic (.position 1 1 3)), #[31, 28, 6, 32, 32, 31, 6, 32, 60, 31, 60, 60, 32, 32, 32, 32, 60, 48, 32, 32, 32, 48, 32, 60, 32, 60, 60, 31, 2, 31]),
    ((.basic (.position 0 1 4)), #[31, 28, 6, 32, 32, 31, 6, 32, 32, 31, 60, 60, 32, 32, 32, 32, 60, 48, 32, 32, 32, 48, 32, 60, 32, 60, 60, 31, 2, 31]),
    ((.basic (.position 1 1 4)), #[31, 28, 6, 32, 32, 31, 6, 32, 32, 31, 60, 60, 32, 32, 32, 32, 60, 48, 32, 32, 32, 48, 32, 32, 32, 60, 60, 31, 2, 31]),
    ((.basic (.position 0 2 3)), #[31, 28, 6, 32, 32, 31, 6, 32, 32, 31, 32, 60, 32, 32, 32, 32, 60, 48, 32, 32, 32, 48, 32, 32, 32, 60, 60, 31, 2, 31]),
    ((.basic (.position 1 2 3)), #[31, 28, 6, 32, 32, 31, 6, 32, 32, 31, 32, 60, 32, 32, 32, 32, 60, 48, 32, 32, 32, 48, 32, 32, 32, 32, 60, 31, 2, 31]),
    ((.basic (.position 0 2 4)), #[31, 28, 6, 32, 32, 31, 6, 32, 32, 31, 32, 32, 32, 32, 32, 32, 60, 48, 32, 32, 32, 48, 32, 32, 32, 32, 60, 31, 2, 31]),
    ((.basic (.position 1 2 4)), #[31, 28, 6, 32, 32, 31, 6, 32, 32, 31, 32, 32, 32, 32, 32, 32, 60, 48, 32, 32, 32, 48, 32, 32, 32, 32, 32, 31, 2, 31]),
    ((.basic (.separation 0 0 1 2)), #[31, 4, 6, 32, 32, 31, 6, 32, 32, 31, 32, 32, 32, 32, 32, 32, 60, 48, 32, 32, 32, 48, 32, 32, 32, 32, 32, 31, 2, 31]),
    ((.basic (.estimate 0 1)), #[31, 4, 6, 32, 32, 31, 6, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 48, 32, 32, 32, 48, 32, 32, 32, 32, 32, 31, 2, 31]),
    (.close 1 0 3 4, #[31, 4, 6, 32, 32, 31, 6, 32, 32, 31, 32, 32, 32, 32, 32, 32, 48, 48, 32, 32, 32, 48, 32, 32, 32, 32, 32, 3, 2, 3])
  ]

theorem d17n0_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 16) d17n0Input d17n0Trace d17n0Final = true := by
  decide +kernel

theorem d17n0_refuted : OrderRefutation (fiveBodySourceDiagram 16) d17n0Input := by
  apply OrderRefutation.trace _ d17n0Final d17n0Trace d17n0_trace_checked
  apply OrderRefutation.branch _ (zwOrderSlot 0 0 2)
  intro a ha
  have domain : d17n0Final (zwOrderSlot 0 0 2) = {1, 2} := by decide +kernel
  rw [domain] at ha
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl
  · have he : Function.update d17n0Final (zwOrderSlot 0 0 2) {1} = d17n1Input := by decide +kernel
    rw [he]
    exact d17n1_refuted
  · have he : Function.update d17n0Final (zwOrderSlot 0 0 2) {2} = d17n2Input := by decide +kernel
    rw [he]
    exact d17n2_refuted

theorem diagram17_refuted : OrderRefutation (fiveBodySourceDiagram 16) (initialOrderBox (fiveBodySourceDiagram 16)) := by
  have he : initialOrderBox (fiveBodySourceDiagram 16) = d17n0Input := by decide +kernel
  rw [he]
  exact d17n0_refuted

theorem diagram17_impossible {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass)
    (i₀ j₀ : Fin 5) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : AdmissibleMasses mass)
    (hd : l.diagramCode = (fiveBodySourceDiagram 16)) : False :=
  impossible_of_orderRefutation q i₀ j₀ hij₀ ha hb l hm _ hd diagram17_refuted

end CentralConfigurations.FiveBodyOrderTreeCertificates
