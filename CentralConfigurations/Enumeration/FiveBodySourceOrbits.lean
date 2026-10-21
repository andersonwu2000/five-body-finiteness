import CentralConfigurations.Enumeration.FiveBodySourceData
import CentralConfigurations.Enumeration.DiagramFingerprint
import Mathlib.Tactic.FinCases

/-! Distinct source orbits are certified by the already proved invariant.
Equal fingerprints are never used to infer isomorphism. -/

namespace CentralConfigurations
set_option maxHeartbeats 0
set_option maxRecDepth 10000
attribute [local irreducible] DiagramCode.orbit

def fiveBodySourceFingerprintValues : Fin 20 → ℕ × ℕ := ![(382553, 389230), (766719, 766719), (481365, 481365), (853056, 853056), (709076, 767169), (882319, 904198), (287647, 620560), (600793, 932045), (25586, 749621), (74985, 600127), (5600, 185635), (40306, 633544), (238642, 508197), (171294, 931341), (550334, 550334), (418399, 463555), (632784, 980454), (47939, 972832), (802442, 802442), (214494, 214494)]

theorem five_body_source_fingerprint_values_injective :
    Function.Injective fiveBodySourceFingerprintValues := by decide +kernel

theorem five_body_source_fingerprint_0 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 0) = fiveBodySourceFingerprintValues 0 := by
  decide +kernel

theorem five_body_source_fingerprint_1 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 1) = fiveBodySourceFingerprintValues 1 := by
  decide +kernel

theorem five_body_source_fingerprint_2 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 2) = fiveBodySourceFingerprintValues 2 := by
  decide +kernel

theorem five_body_source_fingerprint_3 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 3) = fiveBodySourceFingerprintValues 3 := by
  decide +kernel

theorem five_body_source_fingerprint_4 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 4) = fiveBodySourceFingerprintValues 4 := by
  decide +kernel

theorem five_body_source_fingerprint_5 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 5) = fiveBodySourceFingerprintValues 5 := by
  decide +kernel

theorem five_body_source_fingerprint_6 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 6) = fiveBodySourceFingerprintValues 6 := by
  decide +kernel

theorem five_body_source_fingerprint_7 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 7) = fiveBodySourceFingerprintValues 7 := by
  decide +kernel

theorem five_body_source_fingerprint_8 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 8) = fiveBodySourceFingerprintValues 8 := by
  decide +kernel

theorem five_body_source_fingerprint_9 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 9) = fiveBodySourceFingerprintValues 9 := by
  decide +kernel

theorem five_body_source_fingerprint_10 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 10) = fiveBodySourceFingerprintValues 10 := by
  decide +kernel

theorem five_body_source_fingerprint_11 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 11) = fiveBodySourceFingerprintValues 11 := by
  decide +kernel

theorem five_body_source_fingerprint_12 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 12) = fiveBodySourceFingerprintValues 12 := by
  decide +kernel

theorem five_body_source_fingerprint_13 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 13) = fiveBodySourceFingerprintValues 13 := by
  decide +kernel

theorem five_body_source_fingerprint_14 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 14) = fiveBodySourceFingerprintValues 14 := by
  decide +kernel

theorem five_body_source_fingerprint_15 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 15) = fiveBodySourceFingerprintValues 15 := by
  decide +kernel

theorem five_body_source_fingerprint_16 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 16) = fiveBodySourceFingerprintValues 16 := by
  decide +kernel

theorem five_body_source_fingerprint_17 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 17) = fiveBodySourceFingerprintValues 17 := by
  decide +kernel

theorem five_body_source_fingerprint_18 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 18) = fiveBodySourceFingerprintValues 18 := by
  decide +kernel

theorem five_body_source_fingerprint_19 :
    DiagramCode.fingerprint (fiveBodySourceDiagram 19) = fiveBodySourceFingerprintValues 19 := by
  decide +kernel

theorem five_body_source_fingerprint_eq (i : Fin 20) :
    DiagramCode.fingerprint (fiveBodySourceDiagram i) = fiveBodySourceFingerprintValues i := by
  fin_cases i
  · exact five_body_source_fingerprint_0
  · exact five_body_source_fingerprint_1
  · exact five_body_source_fingerprint_2
  · exact five_body_source_fingerprint_3
  · exact five_body_source_fingerprint_4
  · exact five_body_source_fingerprint_5
  · exact five_body_source_fingerprint_6
  · exact five_body_source_fingerprint_7
  · exact five_body_source_fingerprint_8
  · exact five_body_source_fingerprint_9
  · exact five_body_source_fingerprint_10
  · exact five_body_source_fingerprint_11
  · exact five_body_source_fingerprint_12
  · exact five_body_source_fingerprint_13
  · exact five_body_source_fingerprint_14
  · exact five_body_source_fingerprint_15
  · exact five_body_source_fingerprint_16
  · exact five_body_source_fingerprint_17
  · exact five_body_source_fingerprint_18
  · exact five_body_source_fingerprint_19

theorem five_body_source_orbit_index_unique {a b : Fin 20}
    (h : fiveBodySourceDiagram b ∈ DiagramCode.orbit (fiveBodySourceDiagram a)) : a = b := by
  apply five_body_source_fingerprint_values_injective
  rw [← five_body_source_fingerprint_eq a, ← five_body_source_fingerprint_eq b]
  exact (DiagramCode.fingerprint_eq_of_mem_orbit h).symm

theorem five_body_source_number_unique {d : DiagramCode 5} {a b : Fin 20}
    (ha : fiveBodySourceDiagram a ∈ DiagramCode.orbit d)
    (hb : fiveBodySourceDiagram b ∈ DiagramCode.orbit d) : a = b :=
  five_body_source_orbit_index_unique
    (DiagramCode.orbit_transitive (DiagramCode.orbit_symmetric ha) hb)

end CentralConfigurations
