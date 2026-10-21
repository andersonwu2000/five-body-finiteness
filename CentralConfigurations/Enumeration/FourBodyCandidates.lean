import CentralConfigurations.Enumeration.MatchingSearch
import CentralConfigurations.Enumeration.BitMasks

/-!
# Four-body finite candidate certificates

Kernel reduction verifies the executable coverage checks for the integer
candidate lists. This module certifies single-color coverage, the filtered
pair list, and five representatives under common permutations and color
exchange. The FourBody modules derive the corresponding mass restrictions.
-/

namespace CentralConfigurations

def fourBodyMonochromeRepresentatives : Finset (BinaryMatrixCode 4) :=
  ([38, 108, 366, 671, 697, 699, 703, 752, 758, 765, 896, 908, 1006, 1008, 1022, 1023].map
    (BinaryMatrixCode.fromMask 4)).toFinset

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem four_body_monochrome_coverage :
    monochromeCoverageCheck fourBodyMonochromeRepresentatives = true := by
  decide

def fourBodyMatchedCandidates : Finset (DiagramCode 4) :=
  ([(38, 38), (38, 703), (38, 759), (38, 951), (366, 366),
      (697, 725), (697, 915), (896, 19)].map
    (fun p => (BinaryMatrixCode.fromMask 4 p.1, BinaryMatrixCode.fromMask 4 p.2))).toFinset

def fourBodyDiagramRepresentatives : Finset (DiagramCode 4) :=
  ([(38, 38), (38, 703), (366, 366), (697, 725), (896, 19)].map
    (fun p => (BinaryMatrixCode.fromMask 4 p.1, BinaryMatrixCode.fromMask 4 p.2))).toFinset

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
theorem four_body_matched_exhaustion :
    matchedCandidates fourBodyMonochromeRepresentatives = fourBodyMatchedCandidates := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem four_body_pair_orbit_coverage :
    DiagramCode.coverageCheck fourBodyMatchedCandidates fourBodyDiagramRepresentatives = true := by
  decide +kernel

theorem four_body_diagram_coverage :
    DiagramCode.coverageCheck (matchedCandidates fourBodyMonochromeRepresentatives)
      fourBodyDiagramRepresentatives = true := by
  rw [four_body_matched_exhaustion]
  exact four_body_pair_orbit_coverage

theorem four_body_representative_count : fourBodyDiagramRepresentatives.card = 5 := by decide

open scoped Topology
open Filter

/-- The finite certificate is connected to actual singular sequences, rather
than only asserting a cardinality of a detached finite set. -/
theorem four_body_singular_diagram {mass : Fin 4 → ℝ}
    (q : ℕ → NormalizedSystem ℂ 4 (fun i => (mass i : ℂ))) (hm : ∀ i, 0 < mass i)
    (i j : Fin 4) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hu : ¬ BddAbove (Set.range
      (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖))) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
        atTop (𝓝 0) ∧
      ∃ r ∈ fourBodyDiagramRepresentatives, r ∈ DiagramCode.orbit l.leading.diagramCode :=
  matched_representative_of_positive_gauged_unbounded mass q hm i j hij hg hu
    fourBodyMonochromeRepresentatives four_body_monochrome_coverage
    fourBodyDiagramRepresentatives four_body_diagram_coverage

end CentralConfigurations
