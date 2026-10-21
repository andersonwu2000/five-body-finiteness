import CentralConfigurations.Enumeration.BitMasks
import CentralConfigurations.Enumeration.DiagramOrbits
import Mathlib.Data.Fin.VecNotation

/-!
# Figure 9: the twenty five-body source diagrams

Printed p.66 / PDF p.71, visually checked against all twenty source pictures.
Red is z, blue is w and purple records both colors. Source labels 1--5 are
Fin indices 0--4. The extra pair below belongs only to the preliminary search.
-/

namespace CentralConfigurations

def fiveBodySourceMasks : Fin 20 → ℕ × ℕ := ![(11538, 11264), (11742, 11742), (11264, 11264), (11264, 274), (11264, 35), (11264, 11299), (11264, 307), (11264, 11571), (11264, 32544), (11264, 32562), (11264, 32561), (11264, 32433), (11264, 32547), (11264, 32563), (11712, 11712), (11712, 32753), (28672, 613), (28672, 615), (31744, 103), (29280, 22304)]

def fiveBodySourceDiagram (k : Fin 20) : DiagramCode 5 :=
  let p := fiveBodySourceMasks k
  (BinaryMatrixCode.fromMask 5 p.1, BinaryMatrixCode.fromMask 5 p.2)

def fiveBodySourceRepresentatives : Finset (DiagramCode 5) :=
  Finset.univ.image fiveBodySourceDiagram

def fiveBodyExtraDiagram (k : Fin 2) : DiagramCode 5 :=
  let p : ℕ × ℕ := ![(21113, 21173), (21113, 22313)] k
  (BinaryMatrixCode.fromMask 5 p.1, BinaryMatrixCode.fromMask 5 p.2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem five_body_source_diagram_injective : Function.Injective fiveBodySourceDiagram := by
  decide +kernel

theorem five_body_source_count : fiveBodySourceRepresentatives.card = 20 := by
  rw [fiveBodySourceRepresentatives, Finset.card_image_of_injective _ five_body_source_diagram_injective]
  decide

end CentralConfigurations
