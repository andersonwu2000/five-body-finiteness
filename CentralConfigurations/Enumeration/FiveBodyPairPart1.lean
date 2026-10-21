import CentralConfigurations.Enumeration.FiveBodyPairCheck


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row11_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[11]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 11 b k).1 (inputPair 11 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 11 b k) := by
  have he : (survivingRows[11]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row12_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[12]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 12 b k).1 (inputPair 12 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 12 b k) := by
  have he : (survivingRows[12]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row13_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[13]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 13 b k).1 (inputPair 13 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 13 b k) := by
  have he : (survivingRows[13]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row14_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[14]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 14 b k).1 (inputPair 14 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 14 b k) := by
  have he : (survivingRows[14]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a15b9Witnesses : List Nat := [481, 481, 321, 321, 321, 321, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 321, 321, 481, 641, 641, 481, 161, 161, 161, 161, 161, 161, 321, 321, 481, 641, 641, 481, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 481, 641, 321, 321, 481, 641, 481, 641, 321, 321, 481, 641, 161, 161, 161, 161, 161, 161, 481, 641, 321, 321, 481, 641, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a15b9_checked : consecutiveCheck (rowCheck 15 9) 0 a15b9Witnesses = true := by decide +kernel

theorem a15b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 15 9 k).1 (inputPair 15 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 15 9 k) :=
  row_coverage_of_check 15 9 a15b9Witnesses rfl a15b9_checked k hc

def a15b15Witnesses : List Nat := [14, 14, 14, 14, 14, 14, 2762, 2762, 2762, 3562, 3562, 2762, 2762, 3562, 2762, 2762, 2762, 3562, 3562, 2762, 3562, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a15b15_checked : consecutiveCheck (rowCheck 15 15) 0 a15b15Witnesses = true := by decide +kernel

theorem a15b15_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 15 15 k).1 (inputPair 15 15 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 15 15 k) :=
  row_coverage_of_check 15 15 a15b15Witnesses rfl a15b15_checked k hc

def a15b20Witnesses : List Nat := [641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 481, 481, 321, 321, 321, 321, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 321, 321, 481, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 641, 481, 641, 481, 321, 321, 161, 161, 161, 161, 161, 161]

theorem a15b20_checked : consecutiveCheck (rowCheck 15 20) 0 a15b20Witnesses = true := by decide +kernel

theorem a15b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 15 20 k).1 (inputPair 15 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 15 20 k) :=
  row_coverage_of_check 15 20 a15b20Witnesses rfl a15b20_checked k hc

def a15b24Witnesses : List Nat := [2762, 3562, 2762, 3562, 3722, 3722, 3562, 2762, 3722, 3722, 3562, 2762, 3722, 3722, 3562, 2762, 2762, 3562, 2762, 3562, 2762, 3562, 3722, 3722, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a15b24_checked : consecutiveCheck (rowCheck 15 24) 0 a15b24Witnesses = true := by decide +kernel

theorem a15b24_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 15 24 k).1 (inputPair 15 24 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 15 24 k) :=
  row_coverage_of_check 15 24 a15b24Witnesses rfl a15b24_checked k hc

def a15b25Witnesses : List Nat := [321, 321, 321, 321, 481, 481, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 161, 321, 321, 321, 321, 481, 481, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a15b25_checked : consecutiveCheck (rowCheck 15 25) 0 a15b25Witnesses = true := by decide +kernel

theorem a15b25_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 15 25 k).1 (inputPair 15 25 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 15 25 k) :=
  row_coverage_of_check 15 25 a15b25Witnesses rfl a15b25_checked k hc

def a15b27Witnesses : List Nat := [2762, 2762, 2762, 3562, 3562, 2762, 2762, 2762, 2762, 3562, 3562, 2762, 2762, 3562, 2762, 2762, 2762, 3562, 2762, 2762, 2762, 3562, 3562, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a15b27_checked : consecutiveCheck (rowCheck 15 27) 0 a15b27Witnesses = true := by decide +kernel

theorem a15b27_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 15 27 k).1 (inputPair 15 27 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 15 27 k) :=
  row_coverage_of_check 15 27 a15b27Witnesses rfl a15b27_checked k hc

def a15b32Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 3562, 3562, 2762, 2762, 3562, 2762, 2762, 2762, 3562, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a15b32_checked : consecutiveCheck (rowCheck 15 32) 0 a15b32Witnesses = true := by decide +kernel

theorem a15b32_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 15 32 k).1 (inputPair 15 32 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 15 32 k) :=
  row_coverage_of_check 15 32 a15b32Witnesses rfl a15b32_checked k hc

def a15b41Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a15b41_checked : consecutiveCheck (rowCheck 15 41) 0 a15b41Witnesses = true := by decide +kernel

theorem a15b41_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 15 41 k).1 (inputPair 15 41 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 15 41 k) :=
  row_coverage_of_check 15 41 a15b41Witnesses rfl a15b41_checked k hc

def a15b52Witnesses : List Nat := [2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352, 512, 672, 672, 512, 352, 352, 512, 672, 672, 512, 512, 672, 352, 352, 512, 672, 512, 672, 352, 352, 512, 672, 352, 352, 352, 352, 352, 352, 512, 672, 352, 352, 512, 672, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 672, 512, 672, 512, 352, 352, 352, 352, 352, 352, 352, 352]

theorem a15b52_checked : consecutiveCheck (rowCheck 15 52) 0 a15b52Witnesses = true := by decide +kernel

theorem a15b52_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 15 52 k).1 (inputPair 15 52 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 15 52 k) :=
  row_coverage_of_check 15 52 a15b52Witnesses rfl a15b52_checked k hc

theorem row15_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[15]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 15 b k).1 (inputPair 15 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 15 b k) := by
  have he : (survivingRows[15]).toList = [9, 15, 20, 24, 25, 27, 32, 41, 52] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h | h | h | h | h | h | h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a15b9_covered k hc
  · have hbi : b = 15 := Fin.ext h
    subst b
    exact a15b15_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a15b20_covered k hc
  · have hbi : b = 24 := Fin.ext h
    subst b
    exact a15b24_covered k hc
  · have hbi : b = 25 := Fin.ext h
    subst b
    exact a15b25_covered k hc
  · have hbi : b = 27 := Fin.ext h
    subst b
    exact a15b27_covered k hc
  · have hbi : b = 32 := Fin.ext h
    subst b
    exact a15b32_covered k hc
  · have hbi : b = 41 := Fin.ext h
    subst b
    exact a15b41_covered k hc
  · have hbi : b = 52 := Fin.ext h
    subst b
    exact a15b52_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row16_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[16]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 16 b k).1 (inputPair 16 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 16 b k) := by
  have he : (survivingRows[16]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row17_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[17]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 17 b k).1 (inputPair 17 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 17 b k) := by
  have he : (survivingRows[17]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row18_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[18]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 18 b k).1 (inputPair 18 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 18 b k) := by
  have he : (survivingRows[18]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row19_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[19]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 19 b k).1 (inputPair 19 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 19 b k) := by
  have he : (survivingRows[19]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

def a20b9Witnesses : List Nat := [2762, 2762, 2762, 2730, 2730, 2762, 2762, 2762, 2762, 2730, 2730, 2762, 2762, 2570, 2762, 2570, 1770, 1770, 2570, 2762, 1770, 1770, 2570, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 3754, 3754, 2762, 2762, 3722, 2762, 2762, 2762, 3562, 3722, 2762, 3562, 2762, 2762, 2762, 2762, 2762, 2762, 3754, 3754, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 3722, 3562, 2762, 2762, 2762, 2762, 3562, 3722, 2762, 3690, 2762, 3530, 2762, 2762, 2762, 3690, 2762, 3530, 2762, 2762, 2762, 3370, 2762, 3370, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 3690, 2762, 2762, 2762, 3530, 2762, 3690, 2762, 2762, 2762, 3530, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 3370, 2762, 2762, 2762, 3370]

theorem a20b9_checked : consecutiveCheck (rowCheck 20 9) 0 a20b9Witnesses = true := by decide +kernel

theorem a20b9_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 20 9 k).1 (inputPair 20 9 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 20 9 k) :=
  row_coverage_of_check 20 9 a20b9Witnesses rfl a20b9_checked k hc

def a20b20Witnesses : List Nat := [14, 2762, 14, 2762, 2762, 2762, 14, 2762, 14, 2762, 2762, 2762, 14, 2762, 14, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2730, 3530, 2730, 3530, 3690, 3690, 2570, 3370, 1770, 1770, 2570, 3370, 1770, 1770, 2570, 3370, 3370, 2570, 2730, 3530, 2730, 3530, 3690, 3690, 2570, 3370, 1770, 1770, 2570, 3370, 2730, 3530, 2730, 3530, 3690, 3690, 2570, 3370, 1770, 1770, 2570, 3370, 3690, 3690, 3530, 2730, 2730, 3530, 1770, 1770, 2570, 3370, 3370, 2570, 1770, 1770, 2570, 3370, 3370, 2570, 2730, 3530, 2730, 3530, 3690, 3690, 3530, 2730, 3690, 3690, 3530, 2730, 14, 2762, 14, 2762, 2762, 2762, 14, 2762, 14, 2762, 2762, 2762, 14, 2762, 14, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762, 2762]

theorem a20b20_checked : consecutiveCheck (rowCheck 20 20) 0 a20b20Witnesses = true := by decide +kernel

theorem a20b20_covered (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 20 20 k).1 (inputPair 20 20 k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 20 20 k) :=
  row_coverage_of_check 20 20 a20b20Witnesses rfl a20b20_checked k hc

theorem row20_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[20]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 20 b k).1 (inputPair 20 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 20 b k) := by
  have he : (survivingRows[20]).toList = [9, 20] := by decide +kernel
  rw [he] at hb
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with h | h
  · have hbi : b = 9 := Fin.ext h
    subst b
    exact a20b9_covered k hc
  · have hbi : b = 20 := Fin.ext h
    subst b
    exact a20b20_covered k hc

end CentralConfigurations.FiveBodyPairs


set_option maxHeartbeats 0
set_option maxRecDepth 20000

namespace CentralConfigurations.FiveBodyPairs

theorem row21_covered (b : Fin 55) (hb : b.val ∈ (survivingRows[21]).toList) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair 21 b k).1 (inputPair 21 b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair 21 b k) := by
  have he : (survivingRows[21]).toList = [] := by decide +kernel
  rw [he] at hb
  exact (List.not_mem_nil hb).elim

end CentralConfigurations.FiveBodyPairs


