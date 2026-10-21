import CentralConfigurations.Enumeration.FiveBodyPairCheck


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a44b9Witnesses : List Nat := [738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 3138, 3138, 738, 738, 1538, 1538, 738, 738, 738, 738, 2338, 2338, 2338, 2338, 2338, 2338, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 2338, 2338, 2338, 2338, 2338, 2338, 1538, 1538, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 1538, 1538, 1538, 1538, 3138, 3138, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 3138, 3138, 1538, 1538, 3138, 3138, 1538, 1538]

theorem a44b9_checked : consecutiveCheck (rowCheck 44 9) 0 a44b9Witnesses = true := by decide +kernel

theorem a44b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 9 k).1 (inputPair 44 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 9 k) :=
  row_coverage_of_check 44 9 a44b9Witnesses rfl a44b9_checked k hc

def a44b15Witnesses : List Nat := [480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 738, 738, 738, 738, 738, 738, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 738, 738, 1538, 1538, 480, 640, 640, 480, 2338, 2338, 738, 738, 738, 738, 738, 738, 480, 640, 640, 480, 738, 738, 480, 640, 640, 480, 480, 640, 1538, 1538, 480, 640, 480, 640, 738, 738, 480, 640, 738, 738, 2338, 2338, 738, 738, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 1538, 1538, 640, 480, 640, 480, 738, 738, 640, 480, 640, 480, 738, 738, 738, 738, 738, 738, 2338, 2338]

theorem a44b15_checked : consecutiveCheck (rowCheck 44 15) 0 a44b15Witnesses = true := by decide +kernel

theorem a44b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 15 k).1 (inputPair 44 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 15 k) :=
  row_coverage_of_check 44 15 a44b15Witnesses rfl a44b15_checked k hc

def a44b20Witnesses : List Nat := [738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 2338, 2338, 2338, 2338, 2338, 2338, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 2338, 2338, 2338, 2338, 2338, 2338]

theorem a44b20_checked : consecutiveCheck (rowCheck 44 20) 0 a44b20Witnesses = true := by decide +kernel

theorem a44b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 20 k).1 (inputPair 44 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 20 k) :=
  row_coverage_of_check 44 20 a44b20Witnesses rfl a44b20_checked k hc

def a44b23Witnesses : List Nat := [480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 640, 640, 480, 480, 480, 640, 480, 480, 640, 480, 640, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 640, 640, 480, 480, 480, 640, 480, 480, 640, 480, 640, 480, 480, 738, 738, 480, 640, 640, 480, 738, 738, 480, 640, 640, 480, 480, 640, 480, 640, 480, 480, 640, 480, 480, 480, 640, 480, 480, 640, 738, 738, 480, 640, 480, 640, 480, 640, 480, 480, 480, 640, 738, 738, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 3138, 3138, 640, 480, 480, 480, 640, 480, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 3138, 3138]

theorem a44b23_checked : consecutiveCheck (rowCheck 44 23) 0 a44b23Witnesses = true := by decide +kernel

theorem a44b23_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 23 k).1 (inputPair 44 23 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 23 k) :=
  row_coverage_of_check 44 23 a44b23Witnesses rfl a44b23_checked k hc

def a44b24Witnesses : List Nat := [480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 738, 738, 738, 738, 3138, 3138, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 3138, 3138, 738, 738, 480, 640, 640, 480, 738, 738, 3138, 3138, 738, 738, 3138, 3138, 480, 640, 640, 480, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 480, 640, 3138, 3138, 480, 640, 3138, 3138, 738, 738, 738, 738, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 3138, 3138, 640, 480, 640, 480, 738, 738, 640, 480, 640, 480, 738, 738, 738, 738, 738, 738, 3138, 3138]

theorem a44b24_checked : consecutiveCheck (rowCheck 44 24) 0 a44b24Witnesses = true := by decide +kernel

theorem a44b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 24 k).1 (inputPair 44 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 24 k) :=
  row_coverage_of_check 44 24 a44b24Witnesses rfl a44b24_checked k hc

def a44b25Witnesses : List Nat := [480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 738, 738, 738, 738, 1538, 1538, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 2338, 2338, 738, 738, 480, 640, 640, 480, 738, 738, 3138, 3138, 738, 738, 3138, 3138, 480, 640, 640, 480, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 480, 640, 3138, 3138, 480, 640, 3138, 3138, 738, 738, 738, 738, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 2338, 2338, 640, 480, 640, 480, 738, 738, 640, 480, 640, 480, 738, 738, 738, 738, 738, 738, 1538, 1538]

theorem a44b25_checked : consecutiveCheck (rowCheck 44 25) 0 a44b25Witnesses = true := by decide +kernel

theorem a44b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 25 k).1 (inputPair 44 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 25 k) :=
  row_coverage_of_check 44 25 a44b25Witnesses rfl a44b25_checked k hc

def a44b27Witnesses : List Nat := [480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 738, 738, 738, 738, 738, 738, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 738, 738, 738, 738, 480, 640, 640, 480, 738, 738, 738, 738, 738, 738, 738, 738, 480, 640, 640, 480, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 480, 640, 1538, 1538, 480, 640, 2338, 2338, 738, 738, 738, 738, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 1538, 1538, 640, 480, 640, 480, 738, 738, 640, 480, 640, 480, 738, 738, 738, 738, 738, 738, 2338, 2338]

theorem a44b27_checked : consecutiveCheck (rowCheck 44 27) 0 a44b27Witnesses = true := by decide +kernel

theorem a44b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 27 k).1 (inputPair 44 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 27 k) :=
  row_coverage_of_check 44 27 a44b27Witnesses rfl a44b27_checked k hc

def a44b32Witnesses : List Nat := [480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 738, 738, 738, 738, 738, 738, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 738, 738, 738, 738, 480, 640, 640, 480, 738, 738, 738, 738, 738, 738, 738, 738, 480, 640, 640, 480, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 480, 640, 738, 738, 480, 640, 738, 738, 738, 738, 738, 738, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 1538, 1538, 640, 480, 640, 480, 738, 738, 640, 480, 640, 480, 738, 738, 738, 738, 738, 738, 2338, 2338]

theorem a44b32_checked : consecutiveCheck (rowCheck 44 32) 0 a44b32Witnesses = true := by decide +kernel

theorem a44b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 32 k).1 (inputPair 44 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 32 k) :=
  row_coverage_of_check 44 32 a44b32Witnesses rfl a44b32_checked k hc

def a44b35Witnesses : List Nat := [480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 640, 640, 480, 480, 480, 640, 480, 480, 640, 480, 640, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 640, 640, 480, 480, 480, 640, 480, 480, 640, 480, 640, 480, 480, 738, 738, 480, 640, 640, 480, 738, 738, 480, 640, 640, 480, 480, 640, 480, 640, 480, 480, 640, 480, 480, 480, 640, 480, 480, 640, 738, 738, 480, 640, 480, 640, 480, 640, 480, 480, 480, 640, 738, 738, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738, 640, 480, 480, 480, 640, 480, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738]

theorem a44b35_checked : consecutiveCheck (rowCheck 44 35) 0 a44b35Witnesses = true := by decide +kernel

theorem a44b35_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 35 k).1 (inputPair 44 35 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 35 k) :=
  row_coverage_of_check 44 35 a44b35Witnesses rfl a44b35_checked k hc

def a44b36Witnesses : List Nat := [480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 640, 640, 480, 480, 480, 640, 480, 480, 640, 480, 640, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 640, 640, 480, 480, 480, 640, 480, 480, 640, 480, 640, 480, 480, 738, 738, 480, 640, 640, 480, 738, 738, 480, 640, 640, 480, 480, 640, 480, 640, 480, 480, 640, 480, 480, 480, 640, 480, 480, 640, 738, 738, 480, 640, 480, 640, 480, 640, 480, 480, 480, 640, 738, 738, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738, 640, 480, 480, 480, 640, 480, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738]

theorem a44b36_checked : consecutiveCheck (rowCheck 44 36) 0 a44b36Witnesses = true := by decide +kernel

theorem a44b36_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 36 k).1 (inputPair 44 36 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 36 k) :=
  row_coverage_of_check 44 36 a44b36Witnesses rfl a44b36_checked k hc

def a44b41Witnesses : List Nat := [480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 738, 738, 738, 738, 738, 738, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 738, 738, 738, 738, 480, 640, 640, 480, 738, 738, 738, 738, 738, 738, 738, 738, 480, 640, 640, 480, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 480, 640, 738, 738, 480, 640, 738, 738, 738, 738, 738, 738, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 738, 738, 640, 480, 640, 480, 738, 738, 640, 480, 640, 480, 738, 738, 738, 738, 738, 738, 738, 738]

theorem a44b41_checked : consecutiveCheck (rowCheck 44 41) 0 a44b41Witnesses = true := by decide +kernel

theorem a44b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 41 k).1 (inputPair 44 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 41 k) :=
  row_coverage_of_check 44 41 a44b41Witnesses rfl a44b41_checked k hc

def a44b43Witnesses : List Nat := [480, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 357, 357, 480, 640, 357, 357, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 357, 357, 480, 640, 357, 357, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 357, 357, 480, 640, 357, 357, 480, 640, 480, 640, 480, 640, 480, 480, 480, 640, 480, 640, 480, 480, 480, 640, 480, 640, 480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 480, 640, 480, 640, 480, 480, 480, 640, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 480, 640, 480]

theorem a44b43_checked : consecutiveCheck (rowCheck 44 43) 0 a44b43Witnesses = true := by decide +kernel

theorem a44b43_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 43 k).1 (inputPair 44 43 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 43 k) :=
  row_coverage_of_check 44 43 a44b43Witnesses rfl a44b43_checked k hc

def a44b44Witnesses : List Nat := [480, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 3784464, 3784464, 480, 640, 3784464, 3784464, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 1538, 1538, 480, 640, 1538, 1538, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 1538, 1538, 480, 640, 1538, 1538, 480, 640, 480, 640, 480, 640, 480, 480, 480, 640, 480, 640, 480, 480, 480, 640, 480, 640, 480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 480, 640, 480, 640, 480, 480, 480, 640, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 480, 640, 480]

theorem a44b44_checked : consecutiveCheck (rowCheck 44 44) 0 a44b44Witnesses = true := by decide +kernel

theorem a44b44_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 44 k).1 (inputPair 44 44 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 44 k) :=
  row_coverage_of_check 44 44 a44b44Witnesses rfl a44b44_checked k hc

def a44b45Witnesses : List Nat := [480, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738, 480, 640, 738, 738, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738, 480, 640, 738, 738, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738, 480, 640, 738, 738, 480, 640, 480, 640, 480, 640, 480, 480, 480, 640, 480, 640, 480, 480, 480, 640, 480, 640, 480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 480, 640, 480, 640, 480, 480, 480, 640, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 480, 640, 480]

theorem a44b45_checked : consecutiveCheck (rowCheck 44 45) 0 a44b45Witnesses = true := by decide +kernel

theorem a44b45_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 45 k).1 (inputPair 44 45 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 45 k) :=
  row_coverage_of_check 44 45 a44b45Witnesses rfl a44b45_checked k hc

def a44b47Witnesses : List Nat := [480, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738, 480, 640, 738, 738, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738, 480, 640, 738, 738, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 1538, 1538, 480, 640, 1538, 1538, 480, 640, 480, 640, 480, 640, 480, 480, 480, 640, 480, 640, 480, 480, 480, 640, 480, 640, 480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 480, 640, 480, 640, 480, 480, 480, 640, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 480, 640, 480]

theorem a44b47_checked : consecutiveCheck (rowCheck 44 47) 0 a44b47Witnesses = true := by decide +kernel

theorem a44b47_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 47 k).1 (inputPair 44 47 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 47 k) :=
  row_coverage_of_check 44 47 a44b47Witnesses rfl a44b47_checked k hc

def a44b49Witnesses : List Nat := [480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 640, 640, 480, 480, 480, 640, 480, 480, 640, 480, 640, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 640, 640, 480, 480, 480, 640, 480, 480, 640, 480, 640, 480, 480, 738, 738, 480, 640, 640, 480, 738, 738, 480, 640, 640, 480, 480, 640, 480, 640, 480, 480, 640, 480, 480, 480, 640, 480, 480, 640, 738, 738, 480, 640, 480, 640, 480, 640, 480, 480, 480, 640, 738, 738, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738, 640, 480, 480, 480, 640, 480, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738]

theorem a44b49_checked : consecutiveCheck (rowCheck 44 49) 0 a44b49Witnesses = true := by decide +kernel

theorem a44b49_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 49 k).1 (inputPair 44 49 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 49 k) :=
  row_coverage_of_check 44 49 a44b49Witnesses rfl a44b49_checked k hc

def a44b50Witnesses : List Nat := [480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 640, 640, 480, 480, 480, 640, 480, 480, 640, 480, 640, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 640, 480, 480, 640, 640, 480, 480, 480, 640, 480, 480, 640, 480, 640, 480, 480, 738, 738, 480, 640, 640, 480, 738, 738, 480, 640, 640, 480, 480, 640, 480, 640, 480, 480, 640, 480, 480, 480, 640, 480, 480, 640, 738, 738, 480, 640, 480, 640, 480, 640, 480, 480, 480, 640, 738, 738, 480, 640, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738, 640, 480, 480, 480, 640, 480, 480, 480, 640, 480, 480, 640, 640, 480, 640, 480, 738, 738]

theorem a44b50_checked : consecutiveCheck (rowCheck 44 50) 0 a44b50Witnesses = true := by decide +kernel

theorem a44b50_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 50 k).1 (inputPair 44 50 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 50 k) :=
  row_coverage_of_check 44 50 a44b50Witnesses rfl a44b50_checked k hc

def a44b52Witnesses : List Nat := [480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 480, 738, 738, 738, 738, 738, 738, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 738, 738, 738, 738, 480, 640, 640, 480, 738, 738, 738, 738, 738, 738, 738, 738, 480, 640, 640, 480, 738, 738, 480, 640, 640, 480, 480, 640, 738, 738, 480, 640, 480, 640, 738, 738, 480, 640, 738, 738, 738, 738, 738, 738, 480, 640, 738, 738, 480, 640, 640, 480, 640, 480, 738, 738, 640, 480, 640, 480, 738, 738, 640, 480, 640, 480, 738, 738, 738, 738, 738, 738, 738, 738]

theorem a44b52_checked : consecutiveCheck (rowCheck 44 52) 0 a44b52Witnesses = true := by decide +kernel

theorem a44b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 52 k).1 (inputPair 44 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 52 k) :=
  row_coverage_of_check 44 52 a44b52Witnesses rfl a44b52_checked k hc

theorem row44_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[44]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 44 b k).1 (inputPair 44 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 44 b k) := by
  have he : (survivingRows[44]).toList = [9, 15, 20, 23, 24, 25, 27, 32, 35, 36, 41, 43, 44, 45, 47, 49, 50, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a44b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a44b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a44b20_covered k hc
  · have hbi : b = 23 := Fin.ext h
    subst b
    exact a44b23_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a44b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a44b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a44b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a44b32_covered k hc
  · have hbi : b = 35 := Fin.ext h
    subst b
    exact a44b35_covered k hc
  · have hbi : b = 36 := Fin.ext h
    subst b
    exact a44b36_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a44b41_covered k hc
  · have hbi : b = 43 := Fin.ext h
    subst b
    exact a44b43_covered k hc
  · have hbi : b = 44 := Fin.ext h
    subst b
    exact a44b44_covered k hc
  · have hbi : b = 45 := Fin.ext h
    subst b
    exact a44b45_covered k hc
  · have hbi : b = 47 := Fin.ext h
    subst b
    exact a44b47_covered k hc
  · have hbi : b = 49 := Fin.ext h
    subst b
    exact a44b49_covered k hc
  · have hbi : b = 50 := Fin.ext h
    subst b
    exact a44b50_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a44b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a45b9Witnesses : List Nat := [738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 3138, 3138, 738, 738, 1538, 1538, 738, 738, 738, 738, 2338, 2338, 2338, 2338, 2338, 2338, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 2338, 2338, 2338, 2338, 2338, 2338, 1538, 1538, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 1538, 1538, 1538, 1538, 3138, 3138, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 3138, 3138, 1538, 1538, 3138, 3138, 1538, 1538]

theorem a45b9_checked : consecutiveCheck (rowCheck 45 9) 0 a45b9Witnesses = true := by decide +kernel

theorem a45b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 9 k).1 (inputPair 45 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 9 k) :=
  row_coverage_of_check 45 9 a45b9Witnesses rfl a45b9_checked k hc

def a45b15Witnesses : List Nat := [160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 320, 320, 736, 736, 736, 736, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 160, 160, 160, 160, 160, 160, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b15_checked : consecutiveCheck (rowCheck 45 15) 0 a45b15Witnesses = true := by decide +kernel

theorem a45b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 15 k).1 (inputPair 45 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 15 k) :=
  row_coverage_of_check 45 15 a45b15Witnesses rfl a45b15_checked k hc

def a45b20Witnesses : List Nat := [738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 2338, 2338, 2338, 2338, 2338, 2338, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 2338, 2338, 2338, 2338, 2338, 2338]

theorem a45b20_checked : consecutiveCheck (rowCheck 45 20) 0 a45b20Witnesses = true := by decide +kernel

theorem a45b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 20 k).1 (inputPair 45 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 20 k) :=
  row_coverage_of_check 45 20 a45b20Witnesses rfl a45b20_checked k hc

def a45b23Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 2338, 2338, 320, 320, 1538, 1538, 320, 320, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 2338, 2338, 160, 160, 160, 160, 160, 160, 1538, 1538, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 320, 320, 738, 738, 320, 320, 738, 738, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b23_checked : consecutiveCheck (rowCheck 45 23) 0 a45b23Witnesses = true := by decide +kernel

theorem a45b23_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 23 k).1 (inputPair 45 23 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 23 k) :=
  row_coverage_of_check 45 23 a45b23Witnesses rfl a45b23_checked k hc

def a45b24Witnesses : List Nat := [160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 320, 320, 736, 736, 736, 736, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 160, 160, 160, 160, 160, 160, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b24_checked : consecutiveCheck (rowCheck 45 24) 0 a45b24Witnesses = true := by decide +kernel

theorem a45b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 24 k).1 (inputPair 45 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 24 k) :=
  row_coverage_of_check 45 24 a45b24Witnesses rfl a45b24_checked k hc

def a45b25Witnesses : List Nat := [160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 320, 320, 736, 736, 736, 736, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 160, 160, 160, 160, 160, 160, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b25_checked : consecutiveCheck (rowCheck 45 25) 0 a45b25Witnesses = true := by decide +kernel

theorem a45b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 25 k).1 (inputPair 45 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 25 k) :=
  row_coverage_of_check 45 25 a45b25Witnesses rfl a45b25_checked k hc

def a45b27Witnesses : List Nat := [160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 320, 320, 736, 736, 736, 736, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 160, 160, 160, 160, 160, 160, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b27_checked : consecutiveCheck (rowCheck 45 27) 0 a45b27Witnesses = true := by decide +kernel

theorem a45b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 27 k).1 (inputPair 45 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 27 k) :=
  row_coverage_of_check 45 27 a45b27Witnesses rfl a45b27_checked k hc

def a45b32Witnesses : List Nat := [160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 320, 320, 736, 736, 736, 736, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 160, 160, 160, 160, 160, 160, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b32_checked : consecutiveCheck (rowCheck 45 32) 0 a45b32Witnesses = true := by decide +kernel

theorem a45b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 32 k).1 (inputPair 45 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 32 k) :=
  row_coverage_of_check 45 32 a45b32Witnesses rfl a45b32_checked k hc

def a45b35Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 1770, 1770, 320, 320, 1770, 1770, 320, 320, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 1770, 1770, 160, 160, 160, 160, 160, 160, 1770, 1770, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 320, 320, 1770, 1770, 320, 320, 1770, 1770, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b35_checked : consecutiveCheck (rowCheck 45 35) 0 a45b35Witnesses = true := by decide +kernel

theorem a45b35_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 35 k).1 (inputPair 45 35 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 35 k) :=
  row_coverage_of_check 45 35 a45b35Witnesses rfl a45b35_checked k hc

def a45b36Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 738, 738, 320, 320, 738, 738, 320, 320, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 738, 738, 160, 160, 160, 160, 160, 160, 738, 738, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 320, 320, 1538, 1538, 320, 320, 1538, 1538, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b36_checked : consecutiveCheck (rowCheck 45 36) 0 a45b36Witnesses = true := by decide +kernel

theorem a45b36_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 36 k).1 (inputPair 45 36 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 36 k) :=
  row_coverage_of_check 45 36 a45b36Witnesses rfl a45b36_checked k hc

def a45b41Witnesses : List Nat := [160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 320, 320, 736, 736, 736, 736, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 160, 160, 160, 160, 160, 160, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b41_checked : consecutiveCheck (rowCheck 45 41) 0 a45b41Witnesses = true := by decide +kernel

theorem a45b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 41 k).1 (inputPair 45 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 41 k) :=
  row_coverage_of_check 45 41 a45b41Witnesses rfl a45b41_checked k hc

def a45b43Witnesses : List Nat := [3138, 3138, 320, 320, 320, 320, 3138, 3138, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 3138, 3138, 320, 320, 320, 320, 3138, 3138, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 3138, 3138, 320, 320, 320, 320, 3138, 3138, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b43_checked : consecutiveCheck (rowCheck 45 43) 0 a45b43Witnesses = true := by decide +kernel

theorem a45b43_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 43 k).1 (inputPair 45 43 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 43 k) :=
  row_coverage_of_check 45 43 a45b43Witnesses rfl a45b43_checked k hc

def a45b44Witnesses : List Nat := [738, 738, 320, 320, 320, 320, 738, 738, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 1538, 1538, 320, 320, 320, 320, 2338, 2338, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 2338, 2338, 320, 320, 320, 320, 1538, 1538, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b44_checked : consecutiveCheck (rowCheck 45 44) 0 a45b44Witnesses = true := by decide +kernel

theorem a45b44_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 44 k).1 (inputPair 45 44 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 44 k) :=
  row_coverage_of_check 45 44 a45b44Witnesses rfl a45b44_checked k hc

def a45b45Witnesses : List Nat := [3138, 3138, 320, 320, 320, 320, 3138, 3138, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 3138, 3138, 320, 320, 320, 320, 3138, 3138, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 3138, 3138, 320, 320, 320, 320, 3138, 3138, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b45_checked : consecutiveCheck (rowCheck 45 45) 0 a45b45Witnesses = true := by decide +kernel

theorem a45b45_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 45 k).1 (inputPair 45 45 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 45 k) :=
  row_coverage_of_check 45 45 a45b45Witnesses rfl a45b45_checked k hc

def a45b47Witnesses : List Nat := [738, 738, 320, 320, 320, 320, 738, 738, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 738, 738, 320, 320, 320, 320, 738, 738, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 1538, 1538, 320, 320, 320, 320, 1538, 1538, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b47_checked : consecutiveCheck (rowCheck 45 47) 0 a45b47Witnesses = true := by decide +kernel

theorem a45b47_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 47 k).1 (inputPair 45 47 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 47 k) :=
  row_coverage_of_check 45 47 a45b47Witnesses rfl a45b47_checked k hc

def a45b49Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 7, 7, 320, 320, 7, 7, 320, 320, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 7, 7, 160, 160, 160, 160, 160, 160, 7, 7, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 320, 320, 7, 7, 320, 320, 7, 7, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b49_checked : consecutiveCheck (rowCheck 45 49) 0 a45b49Witnesses = true := by decide +kernel

theorem a45b49_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 49 k).1 (inputPair 45 49 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 49 k) :=
  row_coverage_of_check 45 49 a45b49Witnesses rfl a45b49_checked k hc

def a45b50Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 738, 738, 320, 320, 738, 738, 320, 320, 160, 160, 160, 160, 160, 160, 320, 320, 320, 320, 738, 738, 160, 160, 160, 160, 160, 160, 738, 738, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160, 320, 320, 738, 738, 320, 320, 738, 738, 320, 320, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b50_checked : consecutiveCheck (rowCheck 45 50) 0 a45b50Witnesses = true := by decide +kernel

theorem a45b50_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 50 k).1 (inputPair 45 50 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 50 k) :=
  row_coverage_of_check 45 50 a45b50Witnesses rfl a45b50_checked k hc

def a45b52Witnesses : List Nat := [160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 320, 320, 736, 736, 736, 736, 160, 160, 160, 160, 160, 160, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 160, 160, 160, 160, 160, 160, 736, 736, 320, 320, 736, 736, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 736, 736, 736, 736, 320, 320, 160, 160, 160, 160, 160, 160]

theorem a45b52_checked : consecutiveCheck (rowCheck 45 52) 0 a45b52Witnesses = true := by decide +kernel

theorem a45b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 52 k).1 (inputPair 45 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 52 k) :=
  row_coverage_of_check 45 52 a45b52Witnesses rfl a45b52_checked k hc

theorem row45_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[45]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 45 b k).1 (inputPair 45 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 45 b k) := by
  have he : (survivingRows[45]).toList = [9, 15, 20, 23, 24, 25, 27, 32, 35, 36, 41, 43, 44, 45, 47, 49, 50, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a45b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a45b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a45b20_covered k hc
  · have hbi : b = 23 := Fin.ext h
    subst b
    exact a45b23_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a45b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a45b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a45b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a45b32_covered k hc
  · have hbi : b = 35 := Fin.ext h
    subst b
    exact a45b35_covered k hc
  · have hbi : b = 36 := Fin.ext h
    subst b
    exact a45b36_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a45b41_covered k hc
  · have hbi : b = 43 := Fin.ext h
    subst b
    exact a45b43_covered k hc
  · have hbi : b = 44 := Fin.ext h
    subst b
    exact a45b44_covered k hc
  · have hbi : b = 45 := Fin.ext h
    subst b
    exact a45b45_covered k hc
  · have hbi : b = 47 := Fin.ext h
    subst b
    exact a45b47_covered k hc
  · have hbi : b = 49 := Fin.ext h
    subst b
    exact a45b49_covered k hc
  · have hbi : b = 50 := Fin.ext h
    subst b
    exact a45b50_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a45b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row46_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[46]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 46 b k).1 (inputPair 46 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 46 b k) := by
  have he : (survivingRows[46]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a47b9Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b9_checked : consecutiveCheck (rowCheck 47 9) 0 a47b9Witnesses = true := by decide +kernel

theorem a47b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 9 k).1 (inputPair 47 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 9 k) :=
  row_coverage_of_check 47 9 a47b9Witnesses rfl a47b9_checked k hc

def a47b15Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b15_checked : consecutiveCheck (rowCheck 47 15) 0 a47b15Witnesses = true := by decide +kernel

theorem a47b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 15 k).1 (inputPair 47 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 15 k) :=
  row_coverage_of_check 47 15 a47b15Witnesses rfl a47b15_checked k hc

def a47b20Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b20_checked : consecutiveCheck (rowCheck 47 20) 0 a47b20Witnesses = true := by decide +kernel

theorem a47b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 20 k).1 (inputPair 47 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 20 k) :=
  row_coverage_of_check 47 20 a47b20Witnesses rfl a47b20_checked k hc

def a47b23Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b23_checked : consecutiveCheck (rowCheck 47 23) 0 a47b23Witnesses = true := by decide +kernel

theorem a47b23_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 23 k).1 (inputPair 47 23 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 23 k) :=
  row_coverage_of_check 47 23 a47b23Witnesses rfl a47b23_checked k hc

def a47b24Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b24_checked : consecutiveCheck (rowCheck 47 24) 0 a47b24Witnesses = true := by decide +kernel

theorem a47b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 24 k).1 (inputPair 47 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 24 k) :=
  row_coverage_of_check 47 24 a47b24Witnesses rfl a47b24_checked k hc

def a47b25Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b25_checked : consecutiveCheck (rowCheck 47 25) 0 a47b25Witnesses = true := by decide +kernel

theorem a47b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 25 k).1 (inputPair 47 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 25 k) :=
  row_coverage_of_check 47 25 a47b25Witnesses rfl a47b25_checked k hc

def a47b27Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b27_checked : consecutiveCheck (rowCheck 47 27) 0 a47b27Witnesses = true := by decide +kernel

theorem a47b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 27 k).1 (inputPair 47 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 27 k) :=
  row_coverage_of_check 47 27 a47b27Witnesses rfl a47b27_checked k hc

def a47b32Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b32_checked : consecutiveCheck (rowCheck 47 32) 0 a47b32Witnesses = true := by decide +kernel

theorem a47b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 32 k).1 (inputPair 47 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 32 k) :=
  row_coverage_of_check 47 32 a47b32Witnesses rfl a47b32_checked k hc

def a47b35Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b35_checked : consecutiveCheck (rowCheck 47 35) 0 a47b35Witnesses = true := by decide +kernel

theorem a47b35_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 35 k).1 (inputPair 47 35 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 35 k) :=
  row_coverage_of_check 47 35 a47b35Witnesses rfl a47b35_checked k hc

def a47b36Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b36_checked : consecutiveCheck (rowCheck 47 36) 0 a47b36Witnesses = true := by decide +kernel

theorem a47b36_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 36 k).1 (inputPair 47 36 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 36 k) :=
  row_coverage_of_check 47 36 a47b36Witnesses rfl a47b36_checked k hc

def a47b41Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b41_checked : consecutiveCheck (rowCheck 47 41) 0 a47b41Witnesses = true := by decide +kernel

theorem a47b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 41 k).1 (inputPair 47 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 41 k) :=
  row_coverage_of_check 47 41 a47b41Witnesses rfl a47b41_checked k hc

def a47b43Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b43_checked : consecutiveCheck (rowCheck 47 43) 0 a47b43Witnesses = true := by decide +kernel

theorem a47b43_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 43 k).1 (inputPair 47 43 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 43 k) :=
  row_coverage_of_check 47 43 a47b43Witnesses rfl a47b43_checked k hc

def a47b44Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b44_checked : consecutiveCheck (rowCheck 47 44) 0 a47b44Witnesses = true := by decide +kernel

theorem a47b44_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 44 k).1 (inputPair 47 44 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 44 k) :=
  row_coverage_of_check 47 44 a47b44Witnesses rfl a47b44_checked k hc

def a47b45Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b45_checked : consecutiveCheck (rowCheck 47 45) 0 a47b45Witnesses = true := by decide +kernel

theorem a47b45_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 45 k).1 (inputPair 47 45 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 45 k) :=
  row_coverage_of_check 47 45 a47b45Witnesses rfl a47b45_checked k hc

def a47b47Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b47_checked : consecutiveCheck (rowCheck 47 47) 0 a47b47Witnesses = true := by decide +kernel

theorem a47b47_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 47 k).1 (inputPair 47 47 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 47 k) :=
  row_coverage_of_check 47 47 a47b47Witnesses rfl a47b47_checked k hc

def a47b49Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b49_checked : consecutiveCheck (rowCheck 47 49) 0 a47b49Witnesses = true := by decide +kernel

theorem a47b49_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 49 k).1 (inputPair 47 49 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 49 k) :=
  row_coverage_of_check 47 49 a47b49Witnesses rfl a47b49_checked k hc

def a47b50Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b50_checked : consecutiveCheck (rowCheck 47 50) 0 a47b50Witnesses = true := by decide +kernel

theorem a47b50_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 50 k).1 (inputPair 47 50 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 50 k) :=
  row_coverage_of_check 47 50 a47b50Witnesses rfl a47b50_checked k hc

def a47b52Witnesses : List Nat := [904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904, 904]

theorem a47b52_checked : consecutiveCheck (rowCheck 47 52) 0 a47b52Witnesses = true := by decide +kernel

theorem a47b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 52 k).1 (inputPair 47 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 52 k) :=
  row_coverage_of_check 47 52 a47b52Witnesses rfl a47b52_checked k hc

theorem row47_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[47]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 47 b k).1 (inputPair 47 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 47 b k) := by
  have he : (survivingRows[47]).toList = [9, 15, 20, 23, 24, 25, 27, 32, 35, 36, 41, 43, 44, 45, 47, 49, 50, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a47b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a47b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a47b20_covered k hc
  · have hbi : b = 23 := Fin.ext h
    subst b
    exact a47b23_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a47b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a47b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a47b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a47b32_covered k hc
  · have hbi : b = 35 := Fin.ext h
    subst b
    exact a47b35_covered k hc
  · have hbi : b = 36 := Fin.ext h
    subst b
    exact a47b36_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a47b41_covered k hc
  · have hbi : b = 43 := Fin.ext h
    subst b
    exact a47b43_covered k hc
  · have hbi : b = 44 := Fin.ext h
    subst b
    exact a47b44_covered k hc
  · have hbi : b = 45 := Fin.ext h
    subst b
    exact a47b45_covered k hc
  · have hbi : b = 47 := Fin.ext h
    subst b
    exact a47b47_covered k hc
  · have hbi : b = 49 := Fin.ext h
    subst b
    exact a47b49_covered k hc
  · have hbi : b = 50 := Fin.ext h
    subst b
    exact a47b50_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a47b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row48_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[48]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 48 b k).1 (inputPair 48 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 48 b k) := by
  have he : (survivingRows[48]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a49b9Witnesses : List Nat := [481, 481, 321, 321, 321, 321, 481, 481, 321, 321, 321, 321, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 321, 321, 481, 641, 641, 481, 3754, 3754, 3754, 3754, 3754, 3754, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 3754, 3754, 3754, 3754, 3754, 3754, 321, 321, 481, 641, 641, 481, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 481, 641, 321, 321, 481, 641, 673, 513, 673, 513, 353, 353, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 513, 673, 353, 353, 513, 673]

theorem a49b9_checked : consecutiveCheck (rowCheck 49 9) 0 a49b9Witnesses = true := by decide +kernel

theorem a49b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 9 k).1 (inputPair 49 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 9 k) :=
  row_coverage_of_check 49 9 a49b9Witnesses rfl a49b9_checked k hc

def a49b15Witnesses : List Nat := [353, 353, 353, 353, 353, 353, 353, 353, 513, 673, 673, 513, 513, 673, 353, 353, 513, 673, 673, 513, 673, 513, 353, 353, 321, 321, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 321, 321, 481, 641, 641, 481, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 481, 641, 321, 321, 481, 641, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 641, 481, 641, 481, 321, 321]

theorem a49b15_checked : consecutiveCheck (rowCheck 49 15) 0 a49b15Witnesses = true := by decide +kernel

theorem a49b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 15 k).1 (inputPair 49 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 15 k) :=
  row_coverage_of_check 49 15 a49b15Witnesses rfl a49b15_checked k hc

def a49b20Witnesses : List Nat := [641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 6, 6, 6, 6, 6, 6, 321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 321, 321, 481, 641, 641, 481, 321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 481, 481, 321, 321, 321, 321, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 321, 321, 321, 321, 481, 481, 321, 321, 481, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 6, 6, 6, 6, 6, 6]

theorem a49b20_checked : consecutiveCheck (rowCheck 49 20) 0 a49b20Witnesses = true := by decide +kernel

theorem a49b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 20 k).1 (inputPair 49 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 20 k) :=
  row_coverage_of_check 49 20 a49b20Witnesses rfl a49b20_checked k hc

def a49b23Witnesses : List Nat := [937, 905, 937, 905, 873, 873, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 937, 905, 937, 905, 873, 873, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544]

theorem a49b23_checked : consecutiveCheck (rowCheck 49 23) 0 a49b23Witnesses = true := by decide +kernel

theorem a49b23_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 23 k).1 (inputPair 49 23 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 23 k) :=
  row_coverage_of_check 49 23 a49b23Witnesses rfl a49b23_checked k hc

def a49b24Witnesses : List Nat := [673, 513, 673, 513, 353, 353, 513, 673, 353, 353, 513, 673, 353, 353, 513, 673, 673, 513, 673, 513, 673, 513, 353, 353, 641, 481, 641, 481, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 481, 641, 321, 321, 481, 641, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 321, 321, 481, 641, 641, 481, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 641, 481, 641, 481, 321, 321]

theorem a49b24_checked : consecutiveCheck (rowCheck 49 24) 0 a49b24Witnesses = true := by decide +kernel

theorem a49b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 24 k).1 (inputPair 49 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 24 k) :=
  row_coverage_of_check 49 24 a49b24Witnesses rfl a49b24_checked k hc

def a49b25Witnesses : List Nat := [321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 321, 321, 481, 641, 641, 481, 321, 321, 321, 321, 481, 481, 641, 481, 641, 481, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 481, 641, 321, 321, 481, 641, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 321, 321, 481, 641, 641, 481, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 641, 481, 641, 481, 321, 321]

theorem a49b25_checked : consecutiveCheck (rowCheck 49 25) 0 a49b25Witnesses = true := by decide +kernel

theorem a49b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 25 k).1 (inputPair 49 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 25 k) :=
  row_coverage_of_check 49 25 a49b25Witnesses rfl a49b25_checked k hc

def a49b27Witnesses : List Nat := [353, 353, 513, 513, 353, 353, 353, 353, 353, 353, 513, 513, 353, 353, 513, 673, 673, 513, 673, 513, 673, 513, 353, 353, 321, 321, 481, 481, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 321, 321, 321, 321, 481, 481, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 321, 321, 481, 641, 641, 481, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 641, 481, 641, 481, 321, 321]

theorem a49b27_checked : consecutiveCheck (rowCheck 49 27) 0 a49b27Witnesses = true := by decide +kernel

theorem a49b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 27 k).1 (inputPair 49 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 27 k) :=
  row_coverage_of_check 49 27 a49b27Witnesses rfl a49b27_checked k hc

def a49b32Witnesses : List Nat := [353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 513, 513, 353, 353, 353, 353, 513, 513, 673, 513, 673, 513, 353, 353, 321, 321, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 321, 321, 321, 321, 481, 481, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 321, 321, 321, 321, 481, 481, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 641, 481, 641, 481, 321, 321]

theorem a49b32_checked : consecutiveCheck (rowCheck 49 32) 0 a49b32Witnesses = true := by decide +kernel

theorem a49b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 32 k).1 (inputPair 49 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 32 k) :=
  row_coverage_of_check 49 32 a49b32Witnesses rfl a49b32_checked k hc

def a49b35Witnesses : List Nat := [3754, 3754, 3754, 3754, 3754, 3754, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 3754, 3754, 3754, 3754, 3754, 3754, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544]

theorem a49b35_checked : consecutiveCheck (rowCheck 49 35) 0 a49b35Witnesses = true := by decide +kernel

theorem a49b35_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 35 k).1 (inputPair 49 35 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 35 k) :=
  row_coverage_of_check 49 35 a49b35Witnesses rfl a49b35_checked k hc

def a49b36Witnesses : List Nat := [321, 321, 321, 321, 481, 481, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 353, 353, 353, 353, 513, 513, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544]

theorem a49b36_checked : consecutiveCheck (rowCheck 49 36) 0 a49b36Witnesses = true := by decide +kernel

theorem a49b36_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 36 k).1 (inputPair 49 36 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 36 k) :=
  row_coverage_of_check 49 36 a49b36Witnesses rfl a49b36_checked k hc

def a49b41Witnesses : List Nat := [513, 513, 353, 353, 353, 353, 513, 513, 353, 353, 353, 353, 353, 353, 353, 353, 513, 513, 353, 353, 513, 513, 353, 353, 481, 481, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 481, 481, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 321, 321, 321, 321, 481, 481, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 321, 321, 481, 481, 321, 321]

theorem a49b41_checked : consecutiveCheck (rowCheck 49 41) 0 a49b41Witnesses = true := by decide +kernel

theorem a49b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 41 k).1 (inputPair 49 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 41 k) :=
  row_coverage_of_check 49 41 a49b41Witnesses rfl a49b41_checked k hc

def a49b49Witnesses : List Nat := [14, 14, 14, 14, 14, 14, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 14, 14, 14, 14, 14, 14, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544]

theorem a49b49_checked : consecutiveCheck (rowCheck 49 49) 0 a49b49Witnesses = true := by decide +kernel

theorem a49b49_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 49 k).1 (inputPair 49 49 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 49 k) :=
  row_coverage_of_check 49 49 a49b49Witnesses rfl a49b49_checked k hc

def a49b50Witnesses : List Nat := [321, 321, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 353, 353, 353, 353, 353, 353, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544]

theorem a49b50_checked : consecutiveCheck (rowCheck 49 50) 0 a49b50Witnesses = true := by decide +kernel

theorem a49b50_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 50 k).1 (inputPair 49 50 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 50 k) :=
  row_coverage_of_check 49 50 a49b50Witnesses rfl a49b50_checked k hc

def a49b52Witnesses : List Nat := [353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 321, 321, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 321, 321, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 321, 321, 321, 321, 321, 321, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 321, 321, 321, 321, 321, 321]

theorem a49b52_checked : consecutiveCheck (rowCheck 49 52) 0 a49b52Witnesses = true := by decide +kernel

theorem a49b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 52 k).1 (inputPair 49 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 52 k) :=
  row_coverage_of_check 49 52 a49b52Witnesses rfl a49b52_checked k hc

theorem row49_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[49]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 49 b k).1 (inputPair 49 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 49 b k) := by
  have he : (survivingRows[49]).toList = [9, 15, 20, 23, 24, 25, 27, 32, 35, 36, 41, 49, 50, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a49b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a49b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a49b20_covered k hc
  · have hbi : b = 23 := Fin.ext h
    subst b
    exact a49b23_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a49b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a49b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a49b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a49b32_covered k hc
  · have hbi : b = 35 := Fin.ext h
    subst b
    exact a49b35_covered k hc
  · have hbi : b = 36 := Fin.ext h
    subst b
    exact a49b36_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a49b41_covered k hc
  · have hbi : b = 49 := Fin.ext h
    subst b
    exact a49b49_covered k hc
  · have hbi : b = 50 := Fin.ext h
    subst b
    exact a49b50_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a49b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a50b9Witnesses : List Nat := [481, 481, 321, 321, 321, 321, 481, 481, 321, 321, 321, 321, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 321, 321, 481, 641, 641, 481, 2730, 2730, 2730, 3530, 3530, 2730, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 2730, 2730, 2730, 3530, 3530, 2730, 321, 321, 481, 641, 641, 481, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 481, 641, 321, 321, 481, 641, 673, 513, 673, 513, 353, 353, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 513, 673, 353, 353, 513, 673]

theorem a50b9_checked : consecutiveCheck (rowCheck 50 9) 0 a50b9Witnesses = true := by decide +kernel

theorem a50b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 9 k).1 (inputPair 50 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 9 k) :=
  row_coverage_of_check 50 9 a50b9Witnesses rfl a50b9_checked k hc

def a50b15Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 321, 321, 321, 321, 321, 321, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 320, 320, 480, 640, 640, 480, 321, 321, 481, 641, 641, 481, 320, 320, 480, 640, 640, 480, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 480, 640, 320, 320, 480, 640, 481, 641, 321, 321, 481, 641, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 641, 481, 641, 481, 321, 321]

theorem a50b15_checked : consecutiveCheck (rowCheck 50 15) 0 a50b15Witnesses = true := by decide +kernel

theorem a50b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 15 k).1 (inputPair 50 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 15 k) :=
  row_coverage_of_check 50 15 a50b15Witnesses rfl a50b15_checked k hc

def a50b20Witnesses : List Nat := [641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 2730, 2730, 2730, 2730, 2730, 2730, 321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 321, 321, 481, 641, 641, 481, 321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 481, 481, 321, 321, 321, 321, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 321, 321, 321, 321, 481, 481, 321, 321, 481, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 2730, 2730, 2730, 2730, 2730, 2730]

theorem a50b20_checked : consecutiveCheck (rowCheck 50 20) 0 a50b20Witnesses = true := by decide +kernel

theorem a50b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 20 k).1 (inputPair 50 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 20 k) :=
  row_coverage_of_check 50 20 a50b20Witnesses rfl a50b20_checked k hc

def a50b23Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 480, 640, 640, 480, 320, 320, 480, 640, 640, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 480, 640, 320, 320, 480, 640, 320, 320, 320, 320, 480, 480, 480, 640, 320, 320, 480, 640, 480, 480, 320, 320, 320, 320, 640, 480, 640, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 320, 320, 640, 480, 640, 480, 320, 320]

theorem a50b23_checked : consecutiveCheck (rowCheck 50 23) 0 a50b23Witnesses = true := by decide +kernel

theorem a50b23_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 23 k).1 (inputPair 50 23 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 23 k) :=
  row_coverage_of_check 50 23 a50b23Witnesses rfl a50b23_checked k hc

def a50b24Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 641, 481, 641, 481, 321, 321, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 320, 320, 480, 640, 640, 480, 481, 641, 321, 321, 481, 641, 320, 320, 480, 640, 640, 480, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 480, 640, 320, 320, 480, 640, 321, 321, 481, 641, 641, 481, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 641, 481, 641, 481, 321, 321]

theorem a50b24_checked : consecutiveCheck (rowCheck 50 24) 0 a50b24Witnesses = true := by decide +kernel

theorem a50b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 24 k).1 (inputPair 50 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 24 k) :=
  row_coverage_of_check 50 24 a50b24Witnesses rfl a50b24_checked k hc

def a50b25Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 641, 481, 641, 481, 321, 321, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 320, 320, 480, 640, 640, 480, 481, 641, 321, 321, 481, 641, 320, 320, 480, 640, 640, 480, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 480, 640, 320, 320, 480, 640, 321, 321, 481, 641, 641, 481, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 641, 481, 641, 481, 321, 321]

theorem a50b25_checked : consecutiveCheck (rowCheck 50 25) 0 a50b25Witnesses = true := by decide +kernel

theorem a50b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 25 k).1 (inputPair 50 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 25 k) :=
  row_coverage_of_check 50 25 a50b25Witnesses rfl a50b25_checked k hc

def a50b27Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 321, 321, 481, 481, 321, 321, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 320, 320, 480, 640, 640, 480, 321, 321, 321, 321, 481, 481, 320, 320, 480, 640, 640, 480, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 480, 640, 320, 320, 480, 640, 321, 321, 481, 641, 641, 481, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 641, 481, 641, 481, 321, 321]

theorem a50b27_checked : consecutiveCheck (rowCheck 50 27) 0 a50b27Witnesses = true := by decide +kernel

theorem a50b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 27 k).1 (inputPair 50 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 27 k) :=
  row_coverage_of_check 50 27 a50b27Witnesses rfl a50b27_checked k hc

def a50b32Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 321, 321, 321, 321, 321, 321, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 320, 320, 480, 640, 640, 480, 321, 321, 321, 321, 481, 481, 320, 320, 480, 640, 640, 480, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 480, 640, 320, 320, 480, 640, 321, 321, 321, 321, 481, 481, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 641, 481, 641, 481, 321, 321]

theorem a50b32_checked : consecutiveCheck (rowCheck 50 32) 0 a50b32Witnesses = true := by decide +kernel

theorem a50b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 32 k).1 (inputPair 50 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 32 k) :=
  row_coverage_of_check 50 32 a50b32Witnesses rfl a50b32_checked k hc

def a50b35Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 480, 640, 640, 480, 320, 320, 480, 640, 640, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 480, 640, 320, 320, 480, 640, 320, 320, 320, 320, 480, 480, 480, 640, 320, 320, 480, 640, 480, 480, 320, 320, 320, 320, 640, 480, 640, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 320, 320, 640, 480, 640, 480, 320, 320]

theorem a50b35_checked : consecutiveCheck (rowCheck 50 35) 0 a50b35Witnesses = true := by decide +kernel

theorem a50b35_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 35 k).1 (inputPair 50 35 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 35 k) :=
  row_coverage_of_check 50 35 a50b35Witnesses rfl a50b35_checked k hc

def a50b36Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 480, 640, 640, 480, 320, 320, 480, 640, 640, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 480, 640, 320, 320, 480, 640, 320, 320, 320, 320, 480, 480, 480, 640, 320, 320, 480, 640, 480, 480, 320, 320, 320, 320, 640, 480, 640, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 320, 320, 640, 480, 640, 480, 320, 320]

theorem a50b36_checked : consecutiveCheck (rowCheck 50 36) 0 a50b36Witnesses = true := by decide +kernel

theorem a50b36_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 36 k).1 (inputPair 50 36 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 36 k) :=
  row_coverage_of_check 50 36 a50b36Witnesses rfl a50b36_checked k hc

def a50b41Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 481, 481, 321, 321, 321, 321, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 320, 320, 480, 640, 640, 480, 481, 481, 321, 321, 321, 321, 320, 320, 480, 640, 640, 480, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 480, 640, 320, 320, 480, 640, 321, 321, 321, 321, 481, 481, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 321, 321, 481, 481, 321, 321]

theorem a50b41_checked : consecutiveCheck (rowCheck 50 41) 0 a50b41Witnesses = true := by decide +kernel

theorem a50b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 41 k).1 (inputPair 50 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 41 k) :=
  row_coverage_of_check 50 41 a50b41Witnesses rfl a50b41_checked k hc

def a50b49Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 480, 640, 640, 480, 320, 320, 480, 640, 640, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 480, 640, 320, 320, 480, 640, 320, 320, 320, 320, 480, 480, 480, 640, 320, 320, 480, 640, 480, 480, 320, 320, 320, 320, 640, 480, 640, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 320, 320, 640, 480, 640, 480, 320, 320]

theorem a50b49_checked : consecutiveCheck (rowCheck 50 49) 0 a50b49Witnesses = true := by decide +kernel

theorem a50b49_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 49 k).1 (inputPair 50 49 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 49 k) :=
  row_coverage_of_check 50 49 a50b49Witnesses rfl a50b49_checked k hc

def a50b50Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 480, 640, 640, 480, 320, 320, 480, 640, 640, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 480, 640, 320, 320, 480, 640, 320, 320, 320, 320, 480, 480, 480, 640, 320, 320, 480, 640, 480, 480, 320, 320, 320, 320, 640, 480, 640, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 320, 320, 640, 480, 640, 480, 320, 320]

theorem a50b50_checked : consecutiveCheck (rowCheck 50 50) 0 a50b50Witnesses = true := by decide +kernel

theorem a50b50_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 50 k).1 (inputPair 50 50 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 50 k) :=
  row_coverage_of_check 50 50 a50b50Witnesses rfl a50b50_checked k hc

def a50b52Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 321, 321, 321, 321, 321, 321, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 320, 320, 480, 640, 640, 480, 321, 321, 321, 321, 321, 321, 320, 320, 480, 640, 640, 480, 320, 320, 480, 640, 640, 480, 480, 640, 320, 320, 480, 640, 480, 640, 320, 320, 480, 640, 321, 321, 321, 321, 321, 321, 480, 640, 320, 320, 480, 640, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 640, 480, 640, 480, 320, 320, 321, 321, 321, 321, 321, 321]

theorem a50b52_checked : consecutiveCheck (rowCheck 50 52) 0 a50b52Witnesses = true := by decide +kernel

theorem a50b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 52 k).1 (inputPair 50 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 52 k) :=
  row_coverage_of_check 50 52 a50b52Witnesses rfl a50b52_checked k hc

theorem row50_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[50]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 50 b k).1 (inputPair 50 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 50 b k) := by
  have he : (survivingRows[50]).toList = [9, 15, 20, 23, 24, 25, 27, 32, 35, 36, 41, 49, 50, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a50b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a50b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a50b20_covered k hc
  · have hbi : b = 23 := Fin.ext h
    subst b
    exact a50b23_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a50b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a50b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a50b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a50b32_covered k hc
  · have hbi : b = 35 := Fin.ext h
    subst b
    exact a50b35_covered k hc
  · have hbi : b = 36 := Fin.ext h
    subst b
    exact a50b36_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a50b41_covered k hc
  · have hbi : b = 49 := Fin.ext h
    subst b
    exact a50b49_covered k hc
  · have hbi : b = 50 := Fin.ext h
    subst b
    exact a50b50_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a50b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row51_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[51]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 51 b k).1 (inputPair 51 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 51 b k) := by
  have he : (survivingRows[51]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a52b9Witnesses : List Nat := [481, 481, 321, 321, 321, 321, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 481, 641, 321, 321, 481, 641, 161, 161, 161, 161, 161, 161, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a52b9_checked : consecutiveCheck (rowCheck 52 9) 0 a52b9Witnesses = true := by decide +kernel

theorem a52b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 52 9 k).1 (inputPair 52 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 52 9 k) :=
  row_coverage_of_check 52 9 a52b9Witnesses rfl a52b9_checked k hc

def a52b15Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 3562, 3562, 2762, 2762, 3562, 2762, 2762, 2762, 3562, 3562, 2762, 3562, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a52b15_checked : consecutiveCheck (rowCheck 52 15) 0 a52b15Witnesses = true := by decide +kernel

theorem a52b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 52 15 k).1 (inputPair 52 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 52 15 k) :=
  row_coverage_of_check 52 15 a52b15Witnesses rfl a52b15_checked k hc

def a52b20Witnesses : List Nat := [641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 321, 321, 481, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a52b20_checked : consecutiveCheck (rowCheck 52 20) 0 a52b20Witnesses = true := by decide +kernel

theorem a52b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 52 20 k).1 (inputPair 52 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 52 20 k) :=
  row_coverage_of_check 52 20 a52b20Witnesses rfl a52b20_checked k hc

def a52b24Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a52b24_checked : consecutiveCheck (rowCheck 52 24) 0 a52b24Witnesses = true := by decide +kernel

theorem a52b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 52 24 k).1 (inputPair 52 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 52 24 k) :=
  row_coverage_of_check 52 24 a52b24Witnesses rfl a52b24_checked k hc

def a52b25Witnesses : List Nat := [321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a52b25_checked : consecutiveCheck (rowCheck 52 25) 0 a52b25Witnesses = true := by decide +kernel

theorem a52b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 52 25 k).1 (inputPair 52 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 52 25 k) :=
  row_coverage_of_check 52 25 a52b25Witnesses rfl a52b25_checked k hc

def a52b27Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a52b27_checked : consecutiveCheck (rowCheck 52 27) 0 a52b27Witnesses = true := by decide +kernel

theorem a52b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 52 27 k).1 (inputPair 52 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 52 27 k) :=
  row_coverage_of_check 52 27 a52b27Witnesses rfl a52b27_checked k hc

def a52b32Witnesses : List Nat := [3562, 2762, 3562, 2762, 2762, 2762, 3562, 2762, 3562, 2762, 2762, 2762, 3562, 2762, 3562, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a52b32_checked : consecutiveCheck (rowCheck 52 32) 0 a52b32Witnesses = true := by decide +kernel

theorem a52b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 52 32 k).1 (inputPair 52 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 52 32 k) :=
  row_coverage_of_check 52 32 a52b32Witnesses rfl a52b32_checked k hc

def a52b41Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a52b41_checked : consecutiveCheck (rowCheck 52 41) 0 a52b41Witnesses = true := by decide +kernel

theorem a52b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 52 41 k).1 (inputPair 52 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 52 41 k) :=
  row_coverage_of_check 52 41 a52b41Witnesses rfl a52b41_checked k hc

def a52b52Witnesses : List Nat := [14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 14, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a52b52_checked : consecutiveCheck (rowCheck 52 52) 0 a52b52Witnesses = true := by decide +kernel

theorem a52b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 52 52 k).1 (inputPair 52 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 52 52 k) :=
  row_coverage_of_check 52 52 a52b52Witnesses rfl a52b52_checked k hc

theorem row52_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[52]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 52 b k).1 (inputPair 52 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 52 b k) := by
  have he : (survivingRows[52]).toList = [9, 15, 20, 24, 25, 27, 32, 41, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a52b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a52b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a52b20_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a52b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a52b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a52b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a52b32_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a52b41_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a52b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row53_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[53]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 53 b k).1 (inputPair 53 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 53 b k) := by
  have he : (survivingRows[53]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row54_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[54]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 54 b k).1 (inputPair 54 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 54 b k) := by
  have he : (survivingRows[54]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


