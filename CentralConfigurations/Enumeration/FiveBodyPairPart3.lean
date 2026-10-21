import CentralConfigurations.Enumeration.FiveBodyPairCheck


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row33_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[33]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 33 b k).1 (inputPair 33 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 33 b k) := by
  have he : (survivingRows[33]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row34_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[34]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 34 b k).1 (inputPair 34 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 34 b k) := by
  have he : (survivingRows[34]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a35b9Witnesses : List Nat := [481, 481, 321, 321, 321, 321, 481, 481, 321, 321, 321, 321, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 321, 321, 481, 641, 641, 481, 3754, 3754, 3754, 3754, 3754, 3754, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 3754, 3754, 3754, 3754, 3754, 3754, 321, 321, 481, 641, 641, 481, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 481, 641, 321, 321, 481, 641, 673, 513, 673, 513, 353, 353, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 513, 673, 353, 353, 513, 673]

theorem a35b9_checked : consecutiveCheck (rowCheck 35 9) 0 a35b9Witnesses = true := by decide +kernel

theorem a35b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 9 k).1 (inputPair 35 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 9 k) :=
  row_coverage_of_check 35 9 a35b9Witnesses rfl a35b9_checked k hc

def a35b15Witnesses : List Nat := [353, 353, 353, 353, 353, 353, 353, 353, 513, 673, 673, 513, 513, 673, 353, 353, 513, 673, 673, 513, 673, 513, 353, 353, 321, 321, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 321, 321, 481, 641, 641, 481, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 481, 641, 321, 321, 481, 641, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 641, 481, 641, 481, 321, 321]

theorem a35b15_checked : consecutiveCheck (rowCheck 35 15) 0 a35b15Witnesses = true := by decide +kernel

theorem a35b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 15 k).1 (inputPair 35 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 15 k) :=
  row_coverage_of_check 35 15 a35b15Witnesses rfl a35b15_checked k hc

def a35b20Witnesses : List Nat := [641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 3754, 3754, 3754, 3754, 3754, 3754, 321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 321, 321, 481, 641, 641, 481, 321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 481, 481, 321, 321, 321, 321, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 321, 321, 321, 321, 481, 481, 321, 321, 481, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 3754, 3754, 3754, 3754, 3754, 3754]

theorem a35b20_checked : consecutiveCheck (rowCheck 35 20) 0 a35b20Witnesses = true := by decide +kernel

theorem a35b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 20 k).1 (inputPair 35 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 20 k) :=
  row_coverage_of_check 35 20 a35b20Witnesses rfl a35b20_checked k hc

def a35b23Witnesses : List Nat := [937, 905, 937, 905, 873, 873, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 937, 905, 937, 905, 873, 873, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544]

theorem a35b23_checked : consecutiveCheck (rowCheck 35 23) 0 a35b23Witnesses = true := by decide +kernel

theorem a35b23_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 23 k).1 (inputPair 35 23 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 23 k) :=
  row_coverage_of_check 35 23 a35b23Witnesses rfl a35b23_checked k hc

def a35b24Witnesses : List Nat := [673, 513, 673, 513, 353, 353, 513, 673, 353, 353, 513, 673, 353, 353, 513, 673, 673, 513, 673, 513, 673, 513, 353, 353, 641, 481, 641, 481, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 481, 641, 321, 321, 481, 641, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 321, 321, 481, 641, 641, 481, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 641, 481, 641, 481, 321, 321]

theorem a35b24_checked : consecutiveCheck (rowCheck 35 24) 0 a35b24Witnesses = true := by decide +kernel

theorem a35b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 24 k).1 (inputPair 35 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 24 k) :=
  row_coverage_of_check 35 24 a35b24Witnesses rfl a35b24_checked k hc

def a35b25Witnesses : List Nat := [321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 321, 321, 481, 641, 641, 481, 321, 321, 321, 321, 481, 481, 641, 481, 641, 481, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 481, 641, 321, 321, 481, 641, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 321, 321, 481, 641, 641, 481, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 641, 481, 641, 481, 321, 321]

theorem a35b25_checked : consecutiveCheck (rowCheck 35 25) 0 a35b25Witnesses = true := by decide +kernel

theorem a35b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 25 k).1 (inputPair 35 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 25 k) :=
  row_coverage_of_check 35 25 a35b25Witnesses rfl a35b25_checked k hc

def a35b27Witnesses : List Nat := [353, 353, 513, 513, 353, 353, 353, 353, 353, 353, 513, 513, 353, 353, 513, 673, 673, 513, 673, 513, 673, 513, 353, 353, 321, 321, 481, 481, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 321, 321, 321, 321, 481, 481, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 321, 321, 481, 641, 641, 481, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 641, 481, 641, 481, 321, 321]

theorem a35b27_checked : consecutiveCheck (rowCheck 35 27) 0 a35b27Witnesses = true := by decide +kernel

theorem a35b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 27 k).1 (inputPair 35 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 27 k) :=
  row_coverage_of_check 35 27 a35b27Witnesses rfl a35b27_checked k hc

def a35b32Witnesses : List Nat := [353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 513, 513, 353, 353, 353, 353, 513, 513, 673, 513, 673, 513, 353, 353, 321, 321, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 321, 321, 321, 321, 481, 481, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 321, 321, 321, 321, 481, 481, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 641, 481, 641, 481, 321, 321]

theorem a35b32_checked : consecutiveCheck (rowCheck 35 32) 0 a35b32Witnesses = true := by decide +kernel

theorem a35b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 32 k).1 (inputPair 35 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 32 k) :=
  row_coverage_of_check 35 32 a35b32Witnesses rfl a35b32_checked k hc

def a35b35Witnesses : List Nat := [14, 14, 3754, 3754, 3754, 3754, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 14, 14, 3754, 3754, 3754, 3754, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544]

theorem a35b35_checked : consecutiveCheck (rowCheck 35 35) 0 a35b35Witnesses = true := by decide +kernel

theorem a35b35_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 35 k).1 (inputPair 35 35 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 35 k) :=
  row_coverage_of_check 35 35 a35b35Witnesses rfl a35b35_checked k hc

def a35b36Witnesses : List Nat := [321, 321, 321, 321, 481, 481, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 353, 353, 353, 353, 513, 513, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544]

theorem a35b36_checked : consecutiveCheck (rowCheck 35 36) 0 a35b36Witnesses = true := by decide +kernel

theorem a35b36_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 36 k).1 (inputPair 35 36 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 36 k) :=
  row_coverage_of_check 35 36 a35b36Witnesses rfl a35b36_checked k hc

def a35b41Witnesses : List Nat := [513, 513, 353, 353, 353, 353, 513, 513, 353, 353, 353, 353, 353, 353, 353, 353, 513, 513, 353, 353, 513, 513, 353, 353, 481, 481, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 481, 481, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 321, 321, 321, 321, 481, 481, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 321, 321, 481, 481, 321, 321]

theorem a35b41_checked : consecutiveCheck (rowCheck 35 41) 0 a35b41Witnesses = true := by decide +kernel

theorem a35b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 41 k).1 (inputPair 35 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 41 k) :=
  row_coverage_of_check 35 41 a35b41Witnesses rfl a35b41_checked k hc

def a35b49Witnesses : List Nat := [3754, 3754, 3754, 3754, 3754, 3754, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 3754, 3754, 3754, 3754, 3754, 3754, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544]

theorem a35b49_checked : consecutiveCheck (rowCheck 35 49) 0 a35b49Witnesses = true := by decide +kernel

theorem a35b49_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 49 k).1 (inputPair 35 49 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 49 k) :=
  row_coverage_of_check 35 49 a35b49Witnesses rfl a35b49_checked k hc

def a35b50Witnesses : List Nat := [321, 321, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 353, 353, 353, 353, 353, 353, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544, 544, 704, 544, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 704, 544, 544, 544]

theorem a35b50_checked : consecutiveCheck (rowCheck 35 50) 0 a35b50Witnesses = true := by decide +kernel

theorem a35b50_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 50 k).1 (inputPair 35 50 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 50 k) :=
  row_coverage_of_check 35 50 a35b50Witnesses rfl a35b50_checked k hc

def a35b52Witnesses : List Nat := [353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 353, 321, 321, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 544, 544, 544, 704, 704, 544, 321, 321, 321, 321, 321, 321, 544, 544, 544, 704, 704, 544, 544, 544, 544, 704, 704, 544, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 321, 321, 321, 321, 321, 321, 544, 704, 544, 544, 544, 704, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 704, 544, 704, 544, 544, 544, 321, 321, 321, 321, 321, 321]

theorem a35b52_checked : consecutiveCheck (rowCheck 35 52) 0 a35b52Witnesses = true := by decide +kernel

theorem a35b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 52 k).1 (inputPair 35 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 52 k) :=
  row_coverage_of_check 35 52 a35b52Witnesses rfl a35b52_checked k hc

theorem row35_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[35]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 35 b k).1 (inputPair 35 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 35 b k) := by
  have he : (survivingRows[35]).toList = [9, 15, 20, 23, 24, 25, 27, 32, 35, 36, 41, 49, 50, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a35b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a35b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a35b20_covered k hc
  · have hbi : b = 23 := Fin.ext h
    subst b
    exact a35b23_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a35b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a35b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a35b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a35b32_covered k hc
  · have hbi : b = 35 := Fin.ext h
    subst b
    exact a35b35_covered k hc
  · have hbi : b = 36 := Fin.ext h
    subst b
    exact a35b36_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a35b41_covered k hc
  · have hbi : b = 49 := Fin.ext h
    subst b
    exact a35b49_covered k hc
  · have hbi : b = 50 := Fin.ext h
    subst b
    exact a35b50_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a35b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a36b9Witnesses : List Nat := [481, 481, 321, 321, 321, 321, 481, 481, 321, 321, 321, 321, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 321, 321, 481, 641, 641, 481, 2730, 2730, 2730, 3754, 3754, 2730, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 2730, 2730, 2730, 3754, 3754, 2730, 321, 321, 481, 641, 641, 481, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 481, 641, 321, 321, 481, 641, 673, 513, 673, 513, 353, 353, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 513, 673, 353, 353, 513, 673]

theorem a36b9_checked : consecutiveCheck (rowCheck 36 9) 0 a36b9Witnesses = true := by decide +kernel

theorem a36b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 9 k).1 (inputPair 36 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 9 k) :=
  row_coverage_of_check 36 9 a36b9Witnesses rfl a36b9_checked k hc

def a36b15Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 321, 321, 321, 321, 321, 321, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 320, 320, 480, 704, 704, 480, 321, 321, 481, 641, 641, 481, 320, 320, 480, 704, 704, 480, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 480, 704, 320, 320, 480, 704, 481, 641, 321, 321, 481, 641, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 641, 481, 641, 481, 321, 321]

theorem a36b15_checked : consecutiveCheck (rowCheck 36 15) 0 a36b15Witnesses = true := by decide +kernel

theorem a36b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 15 k).1 (inputPair 36 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 15 k) :=
  row_coverage_of_check 36 15 a36b15Witnesses rfl a36b15_checked k hc

def a36b20Witnesses : List Nat := [641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 2730, 2730, 2730, 2730, 2730, 2730, 321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 321, 321, 481, 641, 641, 481, 321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 321, 321, 321, 321, 481, 481, 481, 641, 321, 321, 481, 641, 481, 481, 321, 321, 321, 321, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 321, 321, 321, 321, 481, 481, 321, 321, 481, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 2730, 2730, 2730, 2730, 2730, 2730]

theorem a36b20_checked : consecutiveCheck (rowCheck 36 20) 0 a36b20Witnesses = true := by decide +kernel

theorem a36b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 20 k).1 (inputPair 36 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 20 k) :=
  row_coverage_of_check 36 20 a36b20Witnesses rfl a36b20_checked k hc

def a36b23Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 480, 704, 704, 480, 320, 320, 480, 704, 704, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 480, 704, 320, 320, 480, 704, 320, 320, 320, 320, 480, 480, 480, 704, 320, 320, 480, 704, 480, 480, 320, 320, 320, 320, 704, 480, 704, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 320, 320, 704, 480, 704, 480, 320, 320]

theorem a36b23_checked : consecutiveCheck (rowCheck 36 23) 0 a36b23Witnesses = true := by decide +kernel

theorem a36b23_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 23 k).1 (inputPair 36 23 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 23 k) :=
  row_coverage_of_check 36 23 a36b23Witnesses rfl a36b23_checked k hc

def a36b24Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 641, 481, 641, 481, 321, 321, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 320, 320, 480, 704, 704, 480, 481, 641, 321, 321, 481, 641, 320, 320, 480, 704, 704, 480, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 480, 704, 320, 320, 480, 704, 321, 321, 481, 641, 641, 481, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 641, 481, 641, 481, 321, 321]

theorem a36b24_checked : consecutiveCheck (rowCheck 36 24) 0 a36b24Witnesses = true := by decide +kernel

theorem a36b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 24 k).1 (inputPair 36 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 24 k) :=
  row_coverage_of_check 36 24 a36b24Witnesses rfl a36b24_checked k hc

def a36b25Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 641, 481, 641, 481, 321, 321, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 320, 320, 480, 704, 704, 480, 481, 641, 321, 321, 481, 641, 320, 320, 480, 704, 704, 480, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 480, 704, 320, 320, 480, 704, 321, 321, 481, 641, 641, 481, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 641, 481, 641, 481, 321, 321]

theorem a36b25_checked : consecutiveCheck (rowCheck 36 25) 0 a36b25Witnesses = true := by decide +kernel

theorem a36b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 25 k).1 (inputPair 36 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 25 k) :=
  row_coverage_of_check 36 25 a36b25Witnesses rfl a36b25_checked k hc

def a36b27Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 321, 321, 481, 481, 321, 321, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 320, 320, 480, 704, 704, 480, 321, 321, 321, 321, 481, 481, 320, 320, 480, 704, 704, 480, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 480, 704, 320, 320, 480, 704, 321, 321, 481, 641, 641, 481, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 641, 481, 641, 481, 321, 321]

theorem a36b27_checked : consecutiveCheck (rowCheck 36 27) 0 a36b27Witnesses = true := by decide +kernel

theorem a36b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 27 k).1 (inputPair 36 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 27 k) :=
  row_coverage_of_check 36 27 a36b27Witnesses rfl a36b27_checked k hc

def a36b32Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 321, 321, 321, 321, 321, 321, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 320, 320, 480, 704, 704, 480, 321, 321, 321, 321, 481, 481, 320, 320, 480, 704, 704, 480, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 480, 704, 320, 320, 480, 704, 321, 321, 321, 321, 481, 481, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 641, 481, 641, 481, 321, 321]

theorem a36b32_checked : consecutiveCheck (rowCheck 36 32) 0 a36b32Witnesses = true := by decide +kernel

theorem a36b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 32 k).1 (inputPair 36 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 32 k) :=
  row_coverage_of_check 36 32 a36b32Witnesses rfl a36b32_checked k hc

def a36b35Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 480, 704, 704, 480, 320, 320, 480, 704, 704, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 480, 704, 320, 320, 480, 704, 320, 320, 320, 320, 480, 480, 480, 704, 320, 320, 480, 704, 480, 480, 320, 320, 320, 320, 704, 480, 704, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 320, 320, 704, 480, 704, 480, 320, 320]

theorem a36b35_checked : consecutiveCheck (rowCheck 36 35) 0 a36b35Witnesses = true := by decide +kernel

theorem a36b35_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 35 k).1 (inputPair 36 35 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 35 k) :=
  row_coverage_of_check 36 35 a36b35Witnesses rfl a36b35_checked k hc

def a36b36Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 480, 704, 704, 480, 320, 320, 480, 704, 704, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 480, 704, 320, 320, 480, 704, 320, 320, 320, 320, 480, 480, 480, 704, 320, 320, 480, 704, 480, 480, 320, 320, 320, 320, 704, 480, 704, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 320, 320, 704, 480, 704, 480, 320, 320]

theorem a36b36_checked : consecutiveCheck (rowCheck 36 36) 0 a36b36Witnesses = true := by decide +kernel

theorem a36b36_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 36 k).1 (inputPair 36 36 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 36 k) :=
  row_coverage_of_check 36 36 a36b36Witnesses rfl a36b36_checked k hc

def a36b41Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 481, 481, 321, 321, 321, 321, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 320, 320, 480, 704, 704, 480, 481, 481, 321, 321, 321, 321, 320, 320, 480, 704, 704, 480, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 480, 704, 320, 320, 480, 704, 321, 321, 321, 321, 481, 481, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 321, 321, 481, 481, 321, 321]

theorem a36b41_checked : consecutiveCheck (rowCheck 36 41) 0 a36b41Witnesses = true := by decide +kernel

theorem a36b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 41 k).1 (inputPair 36 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 41 k) :=
  row_coverage_of_check 36 41 a36b41Witnesses rfl a36b41_checked k hc

def a36b49Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 480, 704, 704, 480, 320, 320, 480, 704, 704, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 480, 704, 320, 320, 480, 704, 320, 320, 320, 320, 480, 480, 480, 704, 320, 320, 480, 704, 480, 480, 320, 320, 320, 320, 704, 480, 704, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 320, 320, 704, 480, 704, 480, 320, 320]

theorem a36b49_checked : consecutiveCheck (rowCheck 36 49) 0 a36b49Witnesses = true := by decide +kernel

theorem a36b49_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 49 k).1 (inputPair 36 49 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 49 k) :=
  row_coverage_of_check 36 49 a36b49Witnesses rfl a36b49_checked k hc

def a36b50Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 320, 320, 320, 320, 480, 480, 320, 320, 480, 704, 704, 480, 320, 320, 480, 704, 704, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 480, 704, 320, 320, 480, 704, 320, 320, 320, 320, 480, 480, 480, 704, 320, 320, 480, 704, 480, 480, 320, 320, 320, 320, 704, 480, 704, 480, 320, 320, 320, 320, 480, 480, 320, 320, 480, 480, 320, 320, 320, 320, 704, 480, 704, 480, 320, 320]

theorem a36b50_checked : consecutiveCheck (rowCheck 36 50) 0 a36b50Witnesses = true := by decide +kernel

theorem a36b50_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 50 k).1 (inputPair 36 50 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 50 k) :=
  row_coverage_of_check 36 50 a36b50Witnesses rfl a36b50_checked k hc

def a36b52Witnesses : List Nat := [320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 320, 321, 321, 321, 321, 321, 321, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 320, 320, 480, 704, 704, 480, 321, 321, 321, 321, 321, 321, 320, 320, 480, 704, 704, 480, 320, 320, 480, 704, 704, 480, 480, 704, 320, 320, 480, 704, 480, 704, 320, 320, 480, 704, 321, 321, 321, 321, 321, 321, 480, 704, 320, 320, 480, 704, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 704, 480, 704, 480, 320, 320, 321, 321, 321, 321, 321, 321]

theorem a36b52_checked : consecutiveCheck (rowCheck 36 52) 0 a36b52Witnesses = true := by decide +kernel

theorem a36b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 52 k).1 (inputPair 36 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 52 k) :=
  row_coverage_of_check 36 52 a36b52Witnesses rfl a36b52_checked k hc

theorem row36_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[36]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 36 b k).1 (inputPair 36 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 36 b k) := by
  have he : (survivingRows[36]).toList = [9, 15, 20, 23, 24, 25, 27, 32, 35, 36, 41, 49, 50, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a36b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a36b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a36b20_covered k hc
  · have hbi : b = 23 := Fin.ext h
    subst b
    exact a36b23_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a36b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a36b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a36b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a36b32_covered k hc
  · have hbi : b = 35 := Fin.ext h
    subst b
    exact a36b35_covered k hc
  · have hbi : b = 36 := Fin.ext h
    subst b
    exact a36b36_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a36b41_covered k hc
  · have hbi : b = 49 := Fin.ext h
    subst b
    exact a36b49_covered k hc
  · have hbi : b = 50 := Fin.ext h
    subst b
    exact a36b50_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a36b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row37_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[37]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 37 b k).1 (inputPair 37 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 37 b k) := by
  have he : (survivingRows[37]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row38_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[38]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 38 b k).1 (inputPair 38 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 38 b k) := by
  have he : (survivingRows[38]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row39_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[39]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 39 b k).1 (inputPair 39 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 39 b k) := by
  have he : (survivingRows[39]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row40_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[40]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 40 b k).1 (inputPair 40 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 40 b k) := by
  have he : (survivingRows[40]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a41b9Witnesses : List Nat := [481, 481, 321, 321, 321, 321, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 481, 641, 321, 321, 481, 641, 161, 161, 161, 161, 161, 161, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a41b9_checked : consecutiveCheck (rowCheck 41 9) 0 a41b9Witnesses = true := by decide +kernel

theorem a41b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 41 9 k).1 (inputPair 41 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 41 9 k) :=
  row_coverage_of_check 41 9 a41b9Witnesses rfl a41b9_checked k hc

def a41b15Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 3562, 3562, 2762, 2762, 3562, 2762, 2762, 2762, 3562, 3562, 2762, 3562, 2762, 2762, 2762, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 544, 544, 512, 672, 672, 512, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 512, 672, 544, 544, 512, 672, 512, 512, 512, 512, 512, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 512, 512, 512, 512, 512, 512]

theorem a41b15_checked : consecutiveCheck (rowCheck 41 15) 0 a41b15Witnesses = true := by decide +kernel

theorem a41b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 41 15 k).1 (inputPair 41 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 41 15 k) :=
  row_coverage_of_check 41 15 a41b15Witnesses rfl a41b15_checked k hc

def a41b20Witnesses : List Nat := [641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 321, 321, 481, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a41b20_checked : consecutiveCheck (rowCheck 41 20) 0 a41b20Witnesses = true := by decide +kernel

theorem a41b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 41 20 k).1 (inputPair 41 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 41 20 k) :=
  row_coverage_of_check 41 20 a41b20Witnesses rfl a41b20_checked k hc

def a41b24Witnesses : List Nat := [683, 523, 683, 523, 2762, 2762, 523, 683, 2762, 2762, 523, 683, 2762, 2762, 523, 683, 683, 523, 683, 523, 683, 523, 2762, 2762, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 544, 544, 512, 672, 672, 512, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 512, 672, 544, 544, 512, 672, 512, 512, 512, 512, 512, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 512, 512, 512, 512, 512, 512]

theorem a41b24_checked : consecutiveCheck (rowCheck 41 24) 0 a41b24Witnesses = true := by decide +kernel

theorem a41b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 41 24 k).1 (inputPair 41 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 41 24 k) :=
  row_coverage_of_check 41 24 a41b24Witnesses rfl a41b24_checked k hc

def a41b25Witnesses : List Nat := [321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 544, 544, 512, 672, 672, 512, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 512, 672, 544, 544, 512, 672, 512, 512, 512, 512, 512, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 512, 512, 512, 512, 512, 512]

theorem a41b25_checked : consecutiveCheck (rowCheck 41 25) 0 a41b25Witnesses = true := by decide +kernel

theorem a41b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 41 25 k).1 (inputPair 41 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 41 25 k) :=
  row_coverage_of_check 41 25 a41b25Witnesses rfl a41b25_checked k hc

def a41b27Witnesses : List Nat := [2762, 2762, 2762, 3562, 2762, 2762, 2762, 2762, 2762, 2762, 3562, 2762, 2762, 2762, 2762, 3562, 3722, 3722, 3562, 2762, 3722, 3722, 2762, 2762, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 544, 544, 512, 672, 672, 512, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 512, 672, 544, 544, 512, 672, 512, 512, 512, 512, 512, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 512, 512, 512, 512, 512, 512]

theorem a41b27_checked : consecutiveCheck (rowCheck 41 27) 0 a41b27Witnesses = true := by decide +kernel

theorem a41b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 41 27 k).1 (inputPair 41 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 41 27 k) :=
  row_coverage_of_check 41 27 a41b27Witnesses rfl a41b27_checked k hc

def a41b32Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 3562, 2762, 2762, 2762, 2762, 2762, 2762, 3562, 3562, 2762, 3562, 2762, 2762, 2762, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 544, 544, 512, 672, 672, 512, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 512, 672, 544, 544, 512, 672, 512, 512, 512, 512, 512, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 512, 512, 512, 512, 512, 512]

theorem a41b32_checked : consecutiveCheck (rowCheck 41 32) 0 a41b32Witnesses = true := by decide +kernel

theorem a41b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 41 32 k).1 (inputPair 41 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 41 32 k) :=
  row_coverage_of_check 41 32 a41b32Witnesses rfl a41b32_checked k hc

def a41b41Witnesses : List Nat := [14, 14, 2762, 2762, 2762, 2762, 14, 14, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 14, 14, 2762, 2762, 14, 14, 2762, 2762, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 544, 544, 512, 672, 672, 512, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 512, 672, 544, 544, 512, 672, 512, 512, 512, 512, 512, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 512, 512, 512, 512, 512, 512]

theorem a41b41_checked : consecutiveCheck (rowCheck 41 41) 0 a41b41Witnesses = true := by decide +kernel

theorem a41b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 41 41 k).1 (inputPair 41 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 41 41 k) :=
  row_coverage_of_check 41 41 a41b41Witnesses rfl a41b41_checked k hc

def a41b52Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 544, 544, 512, 672, 672, 512, 512, 512, 512, 512, 512, 512, 544, 544, 512, 672, 672, 512, 544, 544, 512, 672, 672, 512, 512, 672, 544, 544, 512, 672, 512, 672, 544, 544, 512, 672, 512, 512, 512, 512, 512, 512, 512, 672, 544, 544, 512, 672, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 672, 512, 672, 512, 544, 544, 512, 512, 512, 512, 512, 512]

theorem a41b52_checked : consecutiveCheck (rowCheck 41 52) 0 a41b52Witnesses = true := by decide +kernel

theorem a41b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 41 52 k).1 (inputPair 41 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 41 52 k) :=
  row_coverage_of_check 41 52 a41b52Witnesses rfl a41b52_checked k hc

theorem row41_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[41]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 41 b k).1 (inputPair 41 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 41 b k) := by
  have he : (survivingRows[41]).toList = [9, 15, 20, 24, 25, 27, 32, 41, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a41b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a41b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a41b20_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a41b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a41b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a41b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a41b32_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a41b41_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a41b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row42_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[42]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 42 b k).1 (inputPair 42 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 42 b k) := by
  have he : (survivingRows[42]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a43b9Witnesses : List Nat := [738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 3138, 3138, 738, 738, 1538, 1538, 738, 738, 738, 738, 2338, 2338, 2338, 2338, 2338, 2338, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 2338, 2338, 2338, 2338, 2338, 2338, 1538, 1538, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 1538, 1538, 1538, 1538, 3138, 3138, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 3138, 3138, 1538, 1538, 3138, 3138, 1538, 1538]

theorem a43b9_checked : consecutiveCheck (rowCheck 43 9) 0 a43b9Witnesses = true := by decide +kernel

theorem a43b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 9 k).1 (inputPair 43 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 9 k) :=
  row_coverage_of_check 43 9 a43b9Witnesses rfl a43b9_checked k hc

def a43b15Witnesses : List Nat := [1538, 1538, 1538, 1538, 1538, 1538, 2338, 2338, 1538, 1538, 1538, 1538, 1538, 1538, 2338, 2338, 1538, 1538, 1538, 1538, 1538, 1538, 2338, 2338, 738, 738, 738, 738, 738, 738, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 1538, 1538, 736, 736, 736, 736, 2338, 2338, 738, 738, 738, 738, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 2338, 2338, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 738, 738, 738, 738, 2338, 2338]

theorem a43b15_checked : consecutiveCheck (rowCheck 43 15) 0 a43b15Witnesses = true := by decide +kernel

theorem a43b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 15 k).1 (inputPair 43 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 15 k) :=
  row_coverage_of_check 43 15 a43b15Witnesses rfl a43b15_checked k hc

def a43b20Witnesses : List Nat := [738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 2338, 2338, 2338, 2338, 2338, 2338, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 738, 738, 738, 738, 1538, 1538, 2338, 2338, 2338, 2338, 2338, 2338]

theorem a43b20_checked : consecutiveCheck (rowCheck 43 20) 0 a43b20Witnesses = true := by decide +kernel

theorem a43b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 20 k).1 (inputPair 43 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 20 k) :=
  row_coverage_of_check 43 20 a43b20Witnesses rfl a43b20_checked k hc

def a43b23Witnesses : List Nat := [738, 738, 738, 738, 3138, 3138, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 3138, 3138, 738, 738, 738, 738, 3138, 3138, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 3138, 3138, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 736, 736, 2338, 2338, 736, 736, 1538, 1538, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 2338, 2338, 736, 736, 738, 738, 736, 736, 1538, 1538, 736, 736, 736, 736, 736, 736, 736, 736, 3138, 3138, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 736, 736, 3138, 3138]

theorem a43b23_checked : consecutiveCheck (rowCheck 43 23) 0 a43b23Witnesses = true := by decide +kernel

theorem a43b23_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 23 k).1 (inputPair 43 23 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 23 k) :=
  row_coverage_of_check 43 23 a43b23Witnesses rfl a43b23_checked k hc

def a43b24Witnesses : List Nat := [1538, 1538, 1538, 1538, 3138, 3138, 1538, 1538, 3138, 3138, 1538, 1538, 3138, 3138, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 3138, 3138, 738, 738, 738, 738, 3138, 3138, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 3138, 3138, 738, 738, 736, 736, 736, 736, 738, 738, 3138, 3138, 738, 738, 3138, 3138, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 3138, 3138, 736, 736, 3138, 3138, 738, 738, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 3138, 3138, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 738, 738, 738, 738, 3138, 3138]

theorem a43b24_checked : consecutiveCheck (rowCheck 43 24) 0 a43b24Witnesses = true := by decide +kernel

theorem a43b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 24 k).1 (inputPair 43 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 24 k) :=
  row_coverage_of_check 43 24 a43b24Witnesses rfl a43b24_checked k hc

def a43b25Witnesses : List Nat := [738, 738, 738, 738, 738, 738, 738, 738, 3138, 3138, 738, 738, 3138, 3138, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 738, 1538, 1538, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 2338, 2338, 738, 738, 736, 736, 736, 736, 738, 738, 3138, 3138, 738, 738, 3138, 3138, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 3138, 3138, 736, 736, 3138, 3138, 738, 738, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 2338, 2338, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 738, 738, 738, 738, 1538, 1538]

theorem a43b25_checked : consecutiveCheck (rowCheck 43 25) 0 a43b25Witnesses = true := by decide +kernel

theorem a43b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 25 k).1 (inputPair 43 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 25 k) :=
  row_coverage_of_check 43 25 a43b25Witnesses rfl a43b25_checked k hc

def a43b27Witnesses : List Nat := [1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 2338, 2338, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 2338, 2338, 738, 738, 738, 738, 738, 738, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 738, 738, 736, 736, 736, 736, 738, 738, 738, 738, 738, 738, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 1538, 1538, 736, 736, 2338, 2338, 738, 738, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 738, 738, 738, 738, 2338, 2338]

theorem a43b27_checked : consecutiveCheck (rowCheck 43 27) 0 a43b27Witnesses = true := by decide +kernel

theorem a43b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 27 k).1 (inputPair 43 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 27 k) :=
  row_coverage_of_check 43 27 a43b27Witnesses rfl a43b27_checked k hc

def a43b32Witnesses : List Nat := [1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 2338, 2338, 738, 738, 738, 738, 738, 738, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 738, 738, 736, 736, 736, 736, 738, 738, 738, 738, 738, 738, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 738, 738, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 738, 738, 738, 738, 2338, 2338]

theorem a43b32_checked : consecutiveCheck (rowCheck 43 32) 0 a43b32Witnesses = true := by decide +kernel

theorem a43b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 32 k).1 (inputPair 43 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 32 k) :=
  row_coverage_of_check 43 32 a43b32Witnesses rfl a43b32_checked k hc

def a43b35Witnesses : List Nat := [2338, 2338, 2338, 2338, 2338, 2338, 1538, 1538, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 736, 736, 1538, 1538, 2338, 2338, 2338, 2338, 2338, 2338, 1538, 1538, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 736, 736, 1538, 1538, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 736, 736, 3384464, 3384464, 736, 736, 3384464, 3384464, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 3386256, 3386256, 736, 736, 738, 738, 736, 736, 3387536, 3387536, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 3386256, 3386256, 736, 736, 3387536, 3387536, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738]

theorem a43b35_checked : consecutiveCheck (rowCheck 43 35) 0 a43b35Witnesses = true := by decide +kernel

theorem a43b35_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 35 k).1 (inputPair 43 35 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 35 k) :=
  row_coverage_of_check 43 35 a43b35Witnesses rfl a43b35_checked k hc

def a43b36Witnesses : List Nat := [738, 738, 738, 738, 738, 738, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 736, 736, 1538, 1538, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 1538, 1538, 736, 736, 1538, 1538, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738]

theorem a43b36_checked : consecutiveCheck (rowCheck 43 36) 0 a43b36Witnesses = true := by decide +kernel

theorem a43b36_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 36 k).1 (inputPair 43 36 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 36 k) :=
  row_coverage_of_check 43 36 a43b36Witnesses rfl a43b36_checked k hc

def a43b41Witnesses : List Nat := [1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 738, 738, 738, 738, 738, 738, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 738, 738, 736, 736, 736, 736, 738, 738, 738, 738, 738, 738, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 738, 738, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 738, 738, 738, 738, 738, 738]

theorem a43b41_checked : consecutiveCheck (rowCheck 43 41) 0 a43b41Witnesses = true := by decide +kernel

theorem a43b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 41 k).1 (inputPair 43 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 41 k) :=
  row_coverage_of_check 43 41 a43b41Witnesses rfl a43b41_checked k hc

def a43b43Witnesses : List Nat := [3138, 3138, 736, 736, 736, 736, 3138, 3138, 736, 736, 736, 736, 736, 736, 736, 736, 740, 740, 736, 736, 740, 740, 736, 736, 3138, 3138, 736, 736, 736, 736, 3138, 3138, 736, 736, 736, 736, 736, 736, 736, 736, 740, 740, 736, 736, 740, 740, 736, 736, 3138, 3138, 736, 736, 736, 736, 3138, 3138, 736, 736, 736, 736, 736, 736, 736, 736, 740, 740, 736, 736, 740, 740, 736, 736, 736, 736, 736, 736, 740, 740, 736, 736, 736, 736, 740, 740, 736, 736, 736, 736, 740, 740, 740, 740, 740, 740, 740, 740, 736, 736, 740, 740, 736, 736, 736, 736, 740, 740, 736, 736, 740, 740, 740, 740, 740, 740, 736, 736, 740, 740, 736, 736]

theorem a43b43_checked : consecutiveCheck (rowCheck 43 43) 0 a43b43Witnesses = true := by decide +kernel

theorem a43b43_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 43 k).1 (inputPair 43 43 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 43 k) :=
  row_coverage_of_check 43 43 a43b43Witnesses rfl a43b43_checked k hc

def a43b44Witnesses : List Nat := [738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 736, 736, 740, 740, 736, 736, 740, 740, 736, 736, 1538, 1538, 736, 736, 736, 736, 2338, 2338, 736, 736, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 1538, 1538, 736, 736, 2338, 2338, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 1538, 1538, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 740, 740, 738, 738, 740, 740, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 738, 738, 740, 740, 736, 736, 740, 740, 736, 736]

theorem a43b44_checked : consecutiveCheck (rowCheck 43 44) 0 a43b44Witnesses = true := by decide +kernel

theorem a43b44_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 44 k).1 (inputPair 43 44 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 44 k) :=
  row_coverage_of_check 43 44 a43b44Witnesses rfl a43b44_checked k hc

def a43b45Witnesses : List Nat := [3138, 3138, 736, 736, 736, 736, 3138, 3138, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 3138, 3138, 736, 736, 736, 736, 3138, 3138, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 3138, 3138, 736, 736, 736, 736, 3138, 3138, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 1538, 1538, 2338, 2338, 2338, 2338, 2338, 2338, 736, 736, 1538, 1538, 736, 736, 736, 736, 1538, 1538, 736, 736, 2338, 2338, 2338, 2338, 2338, 2338, 736, 736, 1538, 1538, 736, 736]

theorem a43b45_checked : consecutiveCheck (rowCheck 43 45) 0 a43b45Witnesses = true := by decide +kernel

theorem a43b45_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 45 k).1 (inputPair 43 45 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 45 k) :=
  row_coverage_of_check 43 45 a43b45Witnesses rfl a43b45_checked k hc

def a43b47Witnesses : List Nat := [738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 1538, 1538, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 1538, 1538, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 738, 738, 738, 738, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 738, 738, 738, 738, 736, 736, 738, 738, 736, 736]

theorem a43b47_checked : consecutiveCheck (rowCheck 43 47) 0 a43b47Witnesses = true := by decide +kernel

theorem a43b47_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 47 k).1 (inputPair 43 47 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 47 k) :=
  row_coverage_of_check 43 47 a43b47Witnesses rfl a43b47_checked k hc

def a43b49Witnesses : List Nat := [2338, 2338, 2338, 2338, 2338, 2338, 1538, 1538, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 736, 736, 1538, 1538, 2338, 2338, 2338, 2338, 2338, 2338, 1538, 1538, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 736, 736, 1538, 1538, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 736, 736, 3587536, 3587536, 736, 736, 3587536, 3587536, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 3587536, 3587536, 736, 736, 738, 738, 736, 736, 3587536, 3587536, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 3587536, 3587536, 736, 736, 3587536, 3587536, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738]

theorem a43b49_checked : consecutiveCheck (rowCheck 43 49) 0 a43b49Witnesses = true := by decide +kernel

theorem a43b49_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 49 k).1 (inputPair 43 49 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 49 k) :=
  row_coverage_of_check 43 49 a43b49Witnesses rfl a43b49_checked k hc

def a43b50Witnesses : List Nat := [738, 738, 738, 738, 738, 738, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 736, 736, 736, 736, 736, 736, 1538, 1538, 736, 736, 736, 736, 736, 736, 1538, 1538, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 736, 736, 738, 738]

theorem a43b50_checked : consecutiveCheck (rowCheck 43 50) 0 a43b50Witnesses = true := by decide +kernel

theorem a43b50_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 50 k).1 (inputPair 43 50 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 50 k) :=
  row_coverage_of_check 43 50 a43b50Witnesses rfl a43b50_checked k hc

def a43b52Witnesses : List Nat := [1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 1538, 738, 738, 738, 738, 738, 738, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 738, 738, 736, 736, 736, 736, 738, 738, 738, 738, 738, 738, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 738, 738, 738, 738, 738, 738, 736, 736, 738, 738, 736, 736, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 736, 736, 736, 736, 738, 738, 738, 738, 738, 738, 738, 738]

theorem a43b52_checked : consecutiveCheck (rowCheck 43 52) 0 a43b52Witnesses = true := by decide +kernel

theorem a43b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 52 k).1 (inputPair 43 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 52 k) :=
  row_coverage_of_check 43 52 a43b52Witnesses rfl a43b52_checked k hc

theorem row43_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[43]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 43 b k).1 (inputPair 43 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 43 b k) := by
  have he : (survivingRows[43]).toList = [9, 15, 20, 23, 24, 25, 27, 32, 35, 36, 41, 43, 44, 45, 47, 49, 50, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a43b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a43b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a43b20_covered k hc
  · have hbi : b = 23 := Fin.ext h
    subst b
    exact a43b23_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a43b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a43b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a43b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a43b32_covered k hc
  · have hbi : b = 35 := Fin.ext h
    subst b
    exact a43b35_covered k hc
  · have hbi : b = 36 := Fin.ext h
    subst b
    exact a43b36_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a43b41_covered k hc
  · have hbi : b = 43 := Fin.ext h
    subst b
    exact a43b43_covered k hc
  · have hbi : b = 44 := Fin.ext h
    subst b
    exact a43b44_covered k hc
  · have hbi : b = 45 := Fin.ext h
    subst b
    exact a43b45_covered k hc
  · have hbi : b = 47 := Fin.ext h
    subst b
    exact a43b47_covered k hc
  · have hbi : b = 49 := Fin.ext h
    subst b
    exact a43b49_covered k hc
  · have hbi : b = 50 := Fin.ext h
    subst b
    exact a43b50_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a43b52_covered k hc

end CentralConfigurations.FiveBodyPairs


