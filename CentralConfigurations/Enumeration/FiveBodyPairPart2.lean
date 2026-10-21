import CentralConfigurations.Enumeration.FiveBodyPairCheck


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row22_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[22]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 22 b k).1 (inputPair 22 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 22 b k) := by
  have he : (survivingRows[22]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a23b9Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b9_checked : consecutiveCheck (rowCheck 23 9) 0 a23b9Witnesses = true := by decide +kernel

theorem a23b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 9 k).1 (inputPair 23 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 9 k) :=
  row_coverage_of_check 23 9 a23b9Witnesses rfl a23b9_checked k hc

def a23b15Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b15_checked : consecutiveCheck (rowCheck 23 15) 0 a23b15Witnesses = true := by decide +kernel

theorem a23b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 15 k).1 (inputPair 23 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 15 k) :=
  row_coverage_of_check 23 15 a23b15Witnesses rfl a23b15_checked k hc

def a23b20Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b20_checked : consecutiveCheck (rowCheck 23 20) 0 a23b20Witnesses = true := by decide +kernel

theorem a23b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 20 k).1 (inputPair 23 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 20 k) :=
  row_coverage_of_check 23 20 a23b20Witnesses rfl a23b20_checked k hc

def a23b23Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b23_checked : consecutiveCheck (rowCheck 23 23) 0 a23b23Witnesses = true := by decide +kernel

theorem a23b23_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 23 k).1 (inputPair 23 23 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 23 k) :=
  row_coverage_of_check 23 23 a23b23Witnesses rfl a23b23_checked k hc

def a23b24Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b24_checked : consecutiveCheck (rowCheck 23 24) 0 a23b24Witnesses = true := by decide +kernel

theorem a23b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 24 k).1 (inputPair 23 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 24 k) :=
  row_coverage_of_check 23 24 a23b24Witnesses rfl a23b24_checked k hc

def a23b25Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b25_checked : consecutiveCheck (rowCheck 23 25) 0 a23b25Witnesses = true := by decide +kernel

theorem a23b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 25 k).1 (inputPair 23 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 25 k) :=
  row_coverage_of_check 23 25 a23b25Witnesses rfl a23b25_checked k hc

def a23b27Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b27_checked : consecutiveCheck (rowCheck 23 27) 0 a23b27Witnesses = true := by decide +kernel

theorem a23b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 27 k).1 (inputPair 23 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 27 k) :=
  row_coverage_of_check 23 27 a23b27Witnesses rfl a23b27_checked k hc

def a23b32Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b32_checked : consecutiveCheck (rowCheck 23 32) 0 a23b32Witnesses = true := by decide +kernel

theorem a23b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 32 k).1 (inputPair 23 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 32 k) :=
  row_coverage_of_check 23 32 a23b32Witnesses rfl a23b32_checked k hc

def a23b35Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b35_checked : consecutiveCheck (rowCheck 23 35) 0 a23b35Witnesses = true := by decide +kernel

theorem a23b35_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 35 k).1 (inputPair 23 35 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 35 k) :=
  row_coverage_of_check 23 35 a23b35Witnesses rfl a23b35_checked k hc

def a23b36Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b36_checked : consecutiveCheck (rowCheck 23 36) 0 a23b36Witnesses = true := by decide +kernel

theorem a23b36_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 36 k).1 (inputPair 23 36 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 36 k) :=
  row_coverage_of_check 23 36 a23b36Witnesses rfl a23b36_checked k hc

def a23b41Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b41_checked : consecutiveCheck (rowCheck 23 41) 0 a23b41Witnesses = true := by decide +kernel

theorem a23b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 41 k).1 (inputPair 23 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 41 k) :=
  row_coverage_of_check 23 41 a23b41Witnesses rfl a23b41_checked k hc

def a23b49Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b49_checked : consecutiveCheck (rowCheck 23 49) 0 a23b49Witnesses = true := by decide +kernel

theorem a23b49_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 49 k).1 (inputPair 23 49 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 49 k) :=
  row_coverage_of_check 23 49 a23b49Witnesses rfl a23b49_checked k hc

def a23b50Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b50_checked : consecutiveCheck (rowCheck 23 50) 0 a23b50Witnesses = true := by decide +kernel

theorem a23b50_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 50 k).1 (inputPair 23 50 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 50 k) :=
  row_coverage_of_check 23 50 a23b50Witnesses rfl a23b50_checked k hc

def a23b52Witnesses : List Nat := [936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936, 936]

theorem a23b52_checked : consecutiveCheck (rowCheck 23 52) 0 a23b52Witnesses = true := by decide +kernel

theorem a23b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 52 k).1 (inputPair 23 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 52 k) :=
  row_coverage_of_check 23 52 a23b52Witnesses rfl a23b52_checked k hc

theorem row23_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[23]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 23 b k).1 (inputPair 23 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 23 b k) := by
  have he : (survivingRows[23]).toList = [9, 15, 20, 23, 24, 25, 27, 32, 35, 36, 41, 49, 50, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a23b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a23b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a23b20_covered k hc
  · have hbi : b = 23 := Fin.ext h
    subst b
    exact a23b23_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a23b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a23b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a23b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a23b32_covered k hc
  · have hbi : b = 35 := Fin.ext h
    subst b
    exact a23b35_covered k hc
  · have hbi : b = 36 := Fin.ext h
    subst b
    exact a23b36_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a23b41_covered k hc
  · have hbi : b = 49 := Fin.ext h
    subst b
    exact a23b49_covered k hc
  · have hbi : b = 50 := Fin.ext h
    subst b
    exact a23b50_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a23b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a24b9Witnesses : List Nat := [481, 481, 321, 321, 321, 321, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 481, 641, 321, 321, 481, 641, 161, 161, 161, 161, 161, 161, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a24b9_checked : consecutiveCheck (rowCheck 24 9) 0 a24b9Witnesses = true := by decide +kernel

theorem a24b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 24 9 k).1 (inputPair 24 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 24 9 k) :=
  row_coverage_of_check 24 9 a24b9Witnesses rfl a24b9_checked k hc

def a24b15Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 3562, 3562, 3722, 3754, 3754, 3722, 3722, 3754, 3562, 3562, 3722, 3754, 3754, 3722, 3754, 3722, 3562, 3562, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 544, 544, 544, 672, 672, 544, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672, 672, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672]

theorem a24b15_checked : consecutiveCheck (rowCheck 24 15) 0 a24b15Witnesses = true := by decide +kernel

theorem a24b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 24 15 k).1 (inputPair 24 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 24 15 k) :=
  row_coverage_of_check 24 15 a24b15Witnesses rfl a24b15_checked k hc

def a24b20Witnesses : List Nat := [641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 321, 321, 481, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a24b20_checked : consecutiveCheck (rowCheck 24 20) 0 a24b20Witnesses = true := by decide +kernel

theorem a24b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 24 20 k).1 (inputPair 24 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 24 20 k) :=
  row_coverage_of_check 24 20 a24b20Witnesses rfl a24b20_checked k hc

def a24b24Witnesses : List Nat := [14, 3981168, 14, 3981168, 3987568, 3987568, 3981168, 14, 3987568, 3987568, 3981168, 14, 3987568, 3987568, 3981168, 14, 14, 3981168, 14, 3981168, 14, 3981168, 3987568, 3987568, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 544, 544, 544, 672, 672, 544, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672, 672, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672]

theorem a24b24_checked : consecutiveCheck (rowCheck 24 24) 0 a24b24Witnesses = true := by decide +kernel

theorem a24b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 24 24 k).1 (inputPair 24 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 24 24 k) :=
  row_coverage_of_check 24 24 a24b24Witnesses rfl a24b24_checked k hc

def a24b25Witnesses : List Nat := [321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 544, 544, 544, 672, 672, 544, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672, 672, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672]

theorem a24b25_checked : consecutiveCheck (rowCheck 24 25) 0 a24b25Witnesses = true := by decide +kernel

theorem a24b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 24 25 k).1 (inputPair 24 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 24 25 k) :=
  row_coverage_of_check 24 25 a24b25Witnesses rfl a24b25_checked k hc

def a24b27Witnesses : List Nat := [683, 2762, 683, 683, 683, 2762, 2762, 683, 2762, 683, 683, 683, 555, 3562, 555, 683, 683, 3722, 683, 555, 683, 3722, 3562, 555, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 544, 544, 544, 672, 672, 544, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672, 672, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672]

theorem a24b27_checked : consecutiveCheck (rowCheck 24 27) 0 a24b27Witnesses = true := by decide +kernel

theorem a24b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 24 27 k).1 (inputPair 24 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 24 27 k) :=
  row_coverage_of_check 24 27 a24b27Witnesses rfl a24b27_checked k hc

def a24b32Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 3562, 2762, 3562, 3722, 3722, 2762, 3562, 2762, 3562, 3722, 3722, 3754, 3722, 3754, 3722, 3562, 3562, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 544, 544, 544, 672, 672, 544, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672, 672, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672]

theorem a24b32_checked : consecutiveCheck (rowCheck 24 32) 0 a24b32Witnesses = true := by decide +kernel

theorem a24b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 24 32 k).1 (inputPair 24 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 24 32 k) :=
  row_coverage_of_check 24 32 a24b32Witnesses rfl a24b32_checked k hc

def a24b41Witnesses : List Nat := [683, 683, 683, 2762, 2762, 683, 683, 683, 683, 2762, 2762, 683, 2762, 683, 2762, 683, 683, 683, 683, 2762, 683, 683, 683, 2762, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 544, 544, 544, 672, 672, 544, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672, 672, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672]

theorem a24b41_checked : consecutiveCheck (rowCheck 24 41) 0 a24b41Witnesses = true := by decide +kernel

theorem a24b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 24 41 k).1 (inputPair 24 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 24 41 k) :=
  row_coverage_of_check 24 41 a24b41Witnesses rfl a24b41_checked k hc

def a24b52Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 544, 544, 544, 672, 672, 544, 672, 672, 672, 672, 672, 672, 544, 544, 544, 672, 672, 544, 544, 544, 544, 672, 672, 544, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672, 672, 544, 672, 544, 544, 544, 672, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 544, 672, 544, 544, 544, 672, 672, 672, 672, 672, 672]

theorem a24b52_checked : consecutiveCheck (rowCheck 24 52) 0 a24b52Witnesses = true := by decide +kernel

theorem a24b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 24 52 k).1 (inputPair 24 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 24 52 k) :=
  row_coverage_of_check 24 52 a24b52Witnesses rfl a24b52_checked k hc

theorem row24_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[24]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 24 b k).1 (inputPair 24 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 24 b k) := by
  have he : (survivingRows[24]).toList = [9, 15, 20, 24, 25, 27, 32, 41, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a24b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a24b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a24b20_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a24b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a24b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a24b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a24b32_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a24b41_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a24b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a25b9Witnesses : List Nat := [481, 481, 321, 321, 321, 321, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 481, 641, 321, 321, 481, 641, 161, 161, 161, 161, 161, 161, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a25b9_checked : consecutiveCheck (rowCheck 25 9) 0 a25b9Witnesses = true := by decide +kernel

theorem a25b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 25 9 k).1 (inputPair 25 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 25 9 k) :=
  row_coverage_of_check 25 9 a25b9Witnesses rfl a25b9_checked k hc

def a25b15Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 320, 320, 480, 672, 672, 480, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 480, 672, 320, 320, 480, 672, 672, 672, 672, 672, 672, 672, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 672, 672, 672, 672, 672]

theorem a25b15_checked : consecutiveCheck (rowCheck 25 15) 0 a25b15Witnesses = true := by decide +kernel

theorem a25b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 25 15 k).1 (inputPair 25 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 25 15 k) :=
  row_coverage_of_check 25 15 a25b15Witnesses rfl a25b15_checked k hc

def a25b20Witnesses : List Nat := [641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 321, 321, 481, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a25b20_checked : consecutiveCheck (rowCheck 25 20) 0 a25b20Witnesses = true := by decide +kernel

theorem a25b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 25 20 k).1 (inputPair 25 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 25 20 k) :=
  row_coverage_of_check 25 20 a25b20Witnesses rfl a25b20_checked k hc

def a25b24Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 320, 320, 480, 672, 672, 480, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 480, 672, 320, 320, 480, 672, 672, 672, 672, 672, 672, 672, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 672, 672, 672, 672, 672]

theorem a25b24_checked : consecutiveCheck (rowCheck 25 24) 0 a25b24Witnesses = true := by decide +kernel

theorem a25b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 25 24 k).1 (inputPair 25 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 25 24 k) :=
  row_coverage_of_check 25 24 a25b24Witnesses rfl a25b24_checked k hc

def a25b25Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 320, 320, 480, 672, 672, 480, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 480, 672, 320, 320, 480, 672, 672, 672, 672, 672, 672, 672, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 672, 672, 672, 672, 672]

theorem a25b25_checked : consecutiveCheck (rowCheck 25 25) 0 a25b25Witnesses = true := by decide +kernel

theorem a25b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 25 25 k).1 (inputPair 25 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 25 25 k) :=
  row_coverage_of_check 25 25 a25b25Witnesses rfl a25b25_checked k hc

def a25b27Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 320, 320, 480, 672, 672, 480, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 480, 672, 320, 320, 480, 672, 672, 672, 672, 672, 672, 672, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 672, 672, 672, 672, 672]

theorem a25b27_checked : consecutiveCheck (rowCheck 25 27) 0 a25b27Witnesses = true := by decide +kernel

theorem a25b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 25 27 k).1 (inputPair 25 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 25 27 k) :=
  row_coverage_of_check 25 27 a25b27Witnesses rfl a25b27_checked k hc

def a25b32Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 320, 320, 480, 672, 672, 480, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 480, 672, 320, 320, 480, 672, 672, 672, 672, 672, 672, 672, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 672, 672, 672, 672, 672]

theorem a25b32_checked : consecutiveCheck (rowCheck 25 32) 0 a25b32Witnesses = true := by decide +kernel

theorem a25b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 25 32 k).1 (inputPair 25 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 25 32 k) :=
  row_coverage_of_check 25 32 a25b32Witnesses rfl a25b32_checked k hc

def a25b41Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 320, 320, 480, 672, 672, 480, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 480, 672, 320, 320, 480, 672, 672, 672, 672, 672, 672, 672, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 672, 672, 672, 672, 672]

theorem a25b41_checked : consecutiveCheck (rowCheck 25 41) 0 a25b41Witnesses = true := by decide +kernel

theorem a25b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 25 41 k).1 (inputPair 25 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 25 41 k) :=
  row_coverage_of_check 25 41 a25b41Witnesses rfl a25b41_checked k hc

def a25b52Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 320, 320, 480, 672, 672, 480, 672, 672, 672, 672, 672, 672, 320, 320, 480, 672, 672, 480, 320, 320, 480, 672, 672, 480, 480, 672, 320, 320, 480, 672, 480, 672, 320, 320, 480, 672, 672, 672, 672, 672, 672, 672, 480, 672, 320, 320, 480, 672, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 480, 672, 480, 320, 320, 672, 672, 672, 672, 672, 672]

theorem a25b52_checked : consecutiveCheck (rowCheck 25 52) 0 a25b52Witnesses = true := by decide +kernel

theorem a25b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 25 52 k).1 (inputPair 25 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 25 52 k) :=
  row_coverage_of_check 25 52 a25b52Witnesses rfl a25b52_checked k hc

theorem row25_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[25]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 25 b k).1 (inputPair 25 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 25 b k) := by
  have he : (survivingRows[25]).toList = [9, 15, 20, 24, 25, 27, 32, 41, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a25b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a25b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a25b20_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a25b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a25b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a25b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a25b32_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a25b41_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a25b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row26_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[26]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 26 b k).1 (inputPair 26 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 26 b k) := by
  have he : (survivingRows[26]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a27b9Witnesses : List Nat := [481, 481, 321, 321, 321, 321, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 481, 641, 321, 321, 481, 641, 161, 161, 161, 161, 161, 161, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a27b9_checked : consecutiveCheck (rowCheck 27 9) 0 a27b9Witnesses = true := by decide +kernel

theorem a27b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 27 9 k).1 (inputPair 27 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 27 9 k) :=
  row_coverage_of_check 27 9 a27b9Witnesses rfl a27b9_checked k hc

def a27b15Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 3562, 3562, 2762, 2762, 3562, 2762, 2762, 2762, 3562, 3562, 2762, 3562, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 544, 672, 352, 352, 544, 672, 352, 352, 352, 352, 352, 352, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a27b15_checked : consecutiveCheck (rowCheck 27 15) 0 a27b15Witnesses = true := by decide +kernel

theorem a27b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 27 15 k).1 (inputPair 27 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 27 15 k) :=
  row_coverage_of_check 27 15 a27b15Witnesses rfl a27b15_checked k hc

def a27b20Witnesses : List Nat := [641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 321, 321, 481, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a27b20_checked : consecutiveCheck (rowCheck 27 20) 0 a27b20Witnesses = true := by decide +kernel

theorem a27b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 27 20 k).1 (inputPair 27 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 27 20 k) :=
  row_coverage_of_check 27 20 a27b20Witnesses rfl a27b20_checked k hc

def a27b24Witnesses : List Nat := [683, 2762, 683, 2762, 363, 363, 2762, 683, 363, 363, 2762, 683, 363, 363, 2762, 683, 683, 2762, 683, 2762, 683, 2762, 363, 363, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 544, 672, 352, 352, 544, 672, 352, 352, 352, 352, 352, 352, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a27b24_checked : consecutiveCheck (rowCheck 27 24) 0 a27b24Witnesses = true := by decide +kernel

theorem a27b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 27 24 k).1 (inputPair 27 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 27 24 k) :=
  row_coverage_of_check 27 24 a27b24Witnesses rfl a27b24_checked k hc

def a27b25Witnesses : List Nat := [321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 544, 672, 352, 352, 544, 672, 352, 352, 352, 352, 352, 352, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a27b25_checked : consecutiveCheck (rowCheck 27 25) 0 a27b25Witnesses = true := by decide +kernel

theorem a27b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 27 25 k).1 (inputPair 27 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 27 25 k) :=
  row_coverage_of_check 27 25 a27b25Witnesses rfl a27b25_checked k hc

def a27b27Witnesses : List Nat := [14, 2762, 2762, 2762, 3562, 2762, 2762, 14, 2762, 3562, 2762, 2762, 2762, 3562, 2762, 3562, 18764, 2762, 3562, 2762, 18764, 2762, 3562, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 544, 672, 352, 352, 544, 672, 352, 352, 352, 352, 352, 352, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a27b27_checked : consecutiveCheck (rowCheck 27 27) 0 a27b27Witnesses = true := by decide +kernel

theorem a27b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 27 27 k).1 (inputPair 27 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 27 27 k) :=
  row_coverage_of_check 27 27 a27b27Witnesses rfl a27b27_checked k hc

def a27b32Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 3562, 2762, 2762, 2762, 3562, 2762, 2762, 2762, 2762, 3562, 2762, 3562, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 544, 672, 352, 352, 544, 672, 352, 352, 352, 352, 352, 352, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a27b32_checked : consecutiveCheck (rowCheck 27 32) 0 a27b32Witnesses = true := by decide +kernel

theorem a27b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 27 32 k).1 (inputPair 27 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 27 32 k) :=
  row_coverage_of_check 27 32 a27b32Witnesses rfl a27b32_checked k hc

def a27b41Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 544, 672, 352, 352, 544, 672, 352, 352, 352, 352, 352, 352, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a27b41_checked : consecutiveCheck (rowCheck 27 41) 0 a27b41Witnesses = true := by decide +kernel

theorem a27b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 27 41 k).1 (inputPair 27 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 27 41 k) :=
  row_coverage_of_check 27 41 a27b41Witnesses rfl a27b41_checked k hc

def a27b52Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352, 544, 672, 672, 544, 352, 352, 544, 672, 672, 544, 544, 672, 352, 352, 544, 672, 544, 672, 352, 352, 544, 672, 352, 352, 352, 352, 352, 352, 544, 672, 352, 352, 544, 672, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 672, 544, 672, 544, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a27b52_checked : consecutiveCheck (rowCheck 27 52) 0 a27b52Witnesses = true := by decide +kernel

theorem a27b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 27 52 k).1 (inputPair 27 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 27 52 k) :=
  row_coverage_of_check 27 52 a27b52Witnesses rfl a27b52_checked k hc

theorem row27_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[27]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 27 b k).1 (inputPair 27 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 27 b k) := by
  have he : (survivingRows[27]).toList = [9, 15, 20, 24, 25, 27, 32, 41, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a27b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a27b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a27b20_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a27b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a27b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a27b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a27b32_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a27b41_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a27b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row28_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[28]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 28 b k).1 (inputPair 28 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 28 b k) := by
  have he : (survivingRows[28]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row29_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[29]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 29 b k).1 (inputPair 29 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 29 b k) := by
  have he : (survivingRows[29]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row30_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[30]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 30 b k).1 (inputPair 30 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 30 b k) := by
  have he : (survivingRows[30]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row31_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[31]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 31 b k).1 (inputPair 31 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 31 b k) := by
  have he : (survivingRows[31]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a32b9Witnesses : List Nat := [481, 481, 321, 321, 321, 321, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 481, 641, 321, 321, 481, 641, 161, 161, 161, 161, 161, 161, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a32b9_checked : consecutiveCheck (rowCheck 32 9) 0 a32b9Witnesses = true := by decide +kernel

theorem a32b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 32 9 k).1 (inputPair 32 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 32 9 k) :=
  row_coverage_of_check 32 9 a32b9Witnesses rfl a32b9_checked k hc

def a32b15Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 3562, 3562, 2762, 2762, 3562, 2762, 2762, 2762, 3562, 3562, 2762, 3562, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a32b15_checked : consecutiveCheck (rowCheck 32 15) 0 a32b15Witnesses = true := by decide +kernel

theorem a32b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 32 15 k).1 (inputPair 32 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 32 15 k) :=
  row_coverage_of_check 32 15 a32b15Witnesses rfl a32b15_checked k hc

def a32b20Witnesses : List Nat := [641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 321, 321, 481, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a32b20_checked : consecutiveCheck (rowCheck 32 20) 0 a32b20Witnesses = true := by decide +kernel

theorem a32b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 32 20 k).1 (inputPair 32 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 32 20 k) :=
  row_coverage_of_check 32 20 a32b20Witnesses rfl a32b20_checked k hc

def a32b24Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a32b24_checked : consecutiveCheck (rowCheck 32 24) 0 a32b24Witnesses = true := by decide +kernel

theorem a32b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 32 24 k).1 (inputPair 32 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 32 24 k) :=
  row_coverage_of_check 32 24 a32b24Witnesses rfl a32b24_checked k hc

def a32b25Witnesses : List Nat := [321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a32b25_checked : consecutiveCheck (rowCheck 32 25) 0 a32b25Witnesses = true := by decide +kernel

theorem a32b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 32 25 k).1 (inputPair 32 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 32 25 k) :=
  row_coverage_of_check 32 25 a32b25Witnesses rfl a32b25_checked k hc

def a32b27Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a32b27_checked : consecutiveCheck (rowCheck 32 27) 0 a32b27Witnesses = true := by decide +kernel

theorem a32b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 32 27 k).1 (inputPair 32 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 32 27 k) :=
  row_coverage_of_check 32 27 a32b27Witnesses rfl a32b27_checked k hc

def a32b32Witnesses : List Nat := [14, 2762, 14, 2762, 2762, 2762, 3562, 2762, 3722, 2762, 2762, 2762, 3722, 2762, 3562, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a32b32_checked : consecutiveCheck (rowCheck 32 32) 0 a32b32Witnesses = true := by decide +kernel

theorem a32b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 32 32 k).1 (inputPair 32 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 32 32 k) :=
  row_coverage_of_check 32 32 a32b32Witnesses rfl a32b32_checked k hc

def a32b41Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a32b41_checked : consecutiveCheck (rowCheck 32 41) 0 a32b41Witnesses = true := by decide +kernel

theorem a32b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 32 41 k).1 (inputPair 32 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 32 41 k) :=
  row_coverage_of_check 32 41 a32b41Witnesses rfl a32b41_checked k hc

def a32b52Witnesses : List Nat := [3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 3562, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a32b52_checked : consecutiveCheck (rowCheck 32 52) 0 a32b52Witnesses = true := by decide +kernel

theorem a32b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 32 52 k).1 (inputPair 32 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 32 52 k) :=
  row_coverage_of_check 32 52 a32b52Witnesses rfl a32b52_checked k hc

theorem row32_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[32]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 32 b k).1 (inputPair 32 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 32 b k) := by
  have he : (survivingRows[32]).toList = [9, 15, 20, 24, 25, 27, 32, 41, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a32b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a32b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a32b20_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a32b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a32b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a32b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a32b32_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a32b41_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a32b52_covered k hc

end CentralConfigurations.FiveBodyPairs


