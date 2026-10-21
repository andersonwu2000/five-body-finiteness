import CentralConfigurations.Enumeration.OrderRefutationTrees
import CentralConfigurations.Enumeration.FiveBodySourceData

/-!
# Exhaustive checked order refutation of source diagram 9

Generated from an untrusted search tree. All admitted branch values are
covered by proof terms; each update and obstruction is kernel-reduced.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace CentralConfigurations.FiveBodyOrderTreeCertificates

open scoped Topology
open Filter

def d9n0Input : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[31, 60, 60, 60, 60, 31, 60, 60, 6, 31, 8, 8, 31, 8, 31, 31, 60, 60, 60, 60, 32, 60, 60, 48, 32, 8, 8, 32, 8, 32]

def d9n0Final : OrderBox (ZWOrderIndex 5) := codedOrderBox 5 #[4, 4, 8, 8, 4, 3, 8, 8, 2, 8, 8, 8, 8, 8, 3, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]

def d9n0Trace : List (SourceOrderRecord 5) :=
  [
    (.maximal, #[31, 60, 60, 60, 60, 31, 60, 60, 2, 31, 8, 8, 31, 8, 31, 31, 60, 60, 60, 60, 32, 60, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 1)), #[31, 28, 60, 60, 60, 31, 60, 60, 2, 31, 8, 8, 31, 8, 31, 31, 60, 60, 60, 60, 32, 60, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 1 0 1)), #[31, 28, 60, 60, 60, 31, 60, 60, 2, 31, 8, 8, 31, 8, 31, 31, 32, 60, 60, 60, 32, 60, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 2)), #[31, 28, 28, 60, 60, 31, 60, 60, 2, 31, 8, 8, 31, 8, 31, 31, 32, 60, 60, 60, 32, 60, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 1 0 2)), #[31, 28, 28, 60, 60, 31, 60, 60, 2, 31, 8, 8, 31, 8, 31, 31, 32, 32, 60, 60, 32, 60, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 3)), #[31, 28, 28, 28, 60, 31, 60, 60, 2, 31, 8, 8, 31, 8, 31, 31, 32, 32, 60, 60, 32, 60, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 1 0 3)), #[31, 28, 28, 28, 60, 31, 60, 60, 2, 31, 8, 8, 31, 8, 31, 31, 32, 32, 32, 60, 32, 60, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 4)), #[31, 28, 28, 28, 28, 31, 60, 60, 2, 31, 8, 8, 31, 8, 31, 31, 32, 32, 32, 60, 32, 60, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 1 0 4)), #[31, 28, 28, 28, 28, 31, 60, 60, 2, 31, 8, 8, 31, 8, 31, 31, 32, 32, 32, 32, 32, 60, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 1 2)), #[31, 28, 28, 28, 28, 31, 28, 60, 2, 31, 8, 8, 31, 8, 31, 31, 32, 32, 32, 32, 32, 60, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 1 3)), #[31, 28, 28, 28, 28, 31, 28, 28, 2, 31, 8, 8, 31, 8, 31, 31, 32, 32, 32, 32, 32, 60, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 0 1 2 4)), #[31, 28, 28, 28, 28, 31, 8, 28, 2, 31, 8, 8, 31, 8, 31, 31, 32, 32, 32, 32, 32, 60, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 2 4)), #[31, 28, 28, 28, 28, 31, 8, 28, 2, 31, 8, 8, 31, 8, 31, 31, 32, 32, 32, 32, 32, 32, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 0 1 3 4)), #[31, 28, 28, 28, 28, 31, 8, 8, 2, 31, 8, 8, 31, 8, 31, 31, 32, 32, 32, 32, 32, 32, 60, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.separation 1 1 3 4)), #[31, 28, 28, 28, 28, 31, 8, 8, 2, 31, 8, 8, 31, 8, 31, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    (.close 0 1 1 4, #[31, 28, 28, 28, 28, 3, 8, 8, 2, 31, 8, 8, 31, 8, 3, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 1)), #[28, 28, 28, 28, 28, 3, 8, 8, 2, 31, 8, 8, 31, 8, 3, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 1 2)), #[28, 28, 28, 28, 28, 3, 8, 8, 2, 8, 8, 8, 31, 8, 3, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 1 3)), #[28, 28, 28, 28, 28, 3, 8, 8, 2, 8, 8, 8, 8, 8, 3, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    (.remote 0, #[4, 28, 28, 28, 28, 3, 8, 8, 2, 8, 8, 8, 8, 8, 3, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 1)), #[4, 4, 28, 28, 28, 3, 8, 8, 2, 8, 8, 8, 8, 8, 3, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 2)), #[4, 4, 8, 28, 28, 3, 8, 8, 2, 8, 8, 8, 8, 8, 3, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 3)), #[4, 4, 8, 8, 28, 3, 8, 8, 2, 8, 8, 8, 8, 8, 3, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32]),
    ((.basic (.position 0 0 4)), #[4, 4, 8, 8, 4, 3, 8, 8, 2, 8, 8, 8, 8, 8, 3, 31, 32, 32, 32, 32, 32, 32, 32, 32, 32, 8, 8, 32, 8, 32])
  ]

theorem d9n0_trace_checked :
    sourceOrderTraceCheck (fiveBodySourceDiagram 8) d9n0Input d9n0Trace d9n0Final = true := by
  decide +kernel

theorem d9n0_refuted : OrderRefutation (fiveBodySourceDiagram 8) d9n0Input := by
  apply OrderRefutation.trace _ d9n0Final d9n0Trace d9n0_trace_checked
  exact OrderRefutation.leaf _ (.row 0 0) (by decide +kernel)

theorem diagram9_refuted : OrderRefutation (fiveBodySourceDiagram 8) (initialOrderBox (fiveBodySourceDiagram 8)) := by
  have he : initialOrderBox (fiveBodySourceDiagram 8) = d9n0Input := by decide +kernel
  rw [he]
  exact d9n0_refuted

theorem diagram9_impossible {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass)
    (i₀ j₀ : Fin 5) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : AdmissibleMasses mass)
    (hd : l.diagramCode = (fiveBodySourceDiagram 8)) : False :=
  impossible_of_orderRefutation q i₀ j₀ hij₀ ha hb l hm _ hd diagram9_refuted

end CentralConfigurations.FiveBodyOrderTreeCertificates
