import CentralConfigurations.FiveBody.RZeroList

/-! Kernel-checked version of the supplied sorted seven-triple rank certificate.
All 120 labelled seven-subsets are retained. Each branch proves x 0 = 0
from five of its homogeneous additive equations by exact linear arithmetic. -/

namespace CentralConfigurations.FiveBody.RZero

def orderedEquation (x : Fin 5 → ℝ) (e : Fin 10) : Prop :=
  x (complementTriple e 2) = x (complementTriple e 0) + x (complementTriple e 1)

def sevenCandidates : List (Finset (Fin 10)) :=
  [{0,1,2,3,4,5,6},
   {0,1,2,3,4,5,7},
   {0,1,2,3,4,5,8},
   {0,1,2,3,4,5,9},
   {0,1,2,3,4,6,7},
   {0,1,2,3,4,6,8},
   {0,1,2,3,4,6,9},
   {0,1,2,3,4,7,8},
   {0,1,2,3,4,7,9},
   {0,1,2,3,4,8,9},
   {0,1,2,3,5,6,7},
   {0,1,2,3,5,6,8},
   {0,1,2,3,5,6,9},
   {0,1,2,3,5,7,8},
   {0,1,2,3,5,7,9},
   {0,1,2,3,5,8,9},
   {0,1,2,3,6,7,8},
   {0,1,2,3,6,7,9},
   {0,1,2,3,6,8,9},
   {0,1,2,3,7,8,9},
   {0,1,2,4,5,6,7},
   {0,1,2,4,5,6,8},
   {0,1,2,4,5,6,9},
   {0,1,2,4,5,7,8},
   {0,1,2,4,5,7,9},
   {0,1,2,4,5,8,9},
   {0,1,2,4,6,7,8},
   {0,1,2,4,6,7,9},
   {0,1,2,4,6,8,9},
   {0,1,2,4,7,8,9},
   {0,1,2,5,6,7,8},
   {0,1,2,5,6,7,9},
   {0,1,2,5,6,8,9},
   {0,1,2,5,7,8,9},
   {0,1,2,6,7,8,9},
   {0,1,3,4,5,6,7},
   {0,1,3,4,5,6,8},
   {0,1,3,4,5,6,9},
   {0,1,3,4,5,7,8},
   {0,1,3,4,5,7,9},
   {0,1,3,4,5,8,9},
   {0,1,3,4,6,7,8},
   {0,1,3,4,6,7,9},
   {0,1,3,4,6,8,9},
   {0,1,3,4,7,8,9},
   {0,1,3,5,6,7,8},
   {0,1,3,5,6,7,9},
   {0,1,3,5,6,8,9},
   {0,1,3,5,7,8,9},
   {0,1,3,6,7,8,9},
   {0,1,4,5,6,7,8},
   {0,1,4,5,6,7,9},
   {0,1,4,5,6,8,9},
   {0,1,4,5,7,8,9},
   {0,1,4,6,7,8,9},
   {0,1,5,6,7,8,9},
   {0,2,3,4,5,6,7},
   {0,2,3,4,5,6,8},
   {0,2,3,4,5,6,9},
   {0,2,3,4,5,7,8},
   {0,2,3,4,5,7,9},
   {0,2,3,4,5,8,9},
   {0,2,3,4,6,7,8},
   {0,2,3,4,6,7,9},
   {0,2,3,4,6,8,9},
   {0,2,3,4,7,8,9},
   {0,2,3,5,6,7,8},
   {0,2,3,5,6,7,9},
   {0,2,3,5,6,8,9},
   {0,2,3,5,7,8,9},
   {0,2,3,6,7,8,9},
   {0,2,4,5,6,7,8},
   {0,2,4,5,6,7,9},
   {0,2,4,5,6,8,9},
   {0,2,4,5,7,8,9},
   {0,2,4,6,7,8,9},
   {0,2,5,6,7,8,9},
   {0,3,4,5,6,7,8},
   {0,3,4,5,6,7,9},
   {0,3,4,5,6,8,9},
   {0,3,4,5,7,8,9},
   {0,3,4,6,7,8,9},
   {0,3,5,6,7,8,9},
   {0,4,5,6,7,8,9},
   {1,2,3,4,5,6,7},
   {1,2,3,4,5,6,8},
   {1,2,3,4,5,6,9},
   {1,2,3,4,5,7,8},
   {1,2,3,4,5,7,9},
   {1,2,3,4,5,8,9},
   {1,2,3,4,6,7,8},
   {1,2,3,4,6,7,9},
   {1,2,3,4,6,8,9},
   {1,2,3,4,7,8,9},
   {1,2,3,5,6,7,8},
   {1,2,3,5,6,7,9},
   {1,2,3,5,6,8,9},
   {1,2,3,5,7,8,9},
   {1,2,3,6,7,8,9},
   {1,2,4,5,6,7,8},
   {1,2,4,5,6,7,9},
   {1,2,4,5,6,8,9},
   {1,2,4,5,7,8,9},
   {1,2,4,6,7,8,9},
   {1,2,5,6,7,8,9},
   {1,3,4,5,6,7,8},
   {1,3,4,5,6,7,9},
   {1,3,4,5,6,8,9},
   {1,3,4,5,7,8,9},
   {1,3,4,6,7,8,9},
   {1,3,5,6,7,8,9},
   {1,4,5,6,7,8,9},
   {2,3,4,5,6,7,8},
   {2,3,4,5,6,7,9},
   {2,3,4,5,6,8,9},
   {2,3,4,5,7,8,9},
   {2,3,4,6,7,8,9},
   {2,3,5,6,7,8,9},
   {2,4,5,6,7,8,9},
   {3,4,5,6,7,8,9}]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem seven_candidates_complete (s : Finset (Fin 10)) (hs : s.card = 7) :
    s ∈ sevenCandidates := by
  revert s
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem seven_constraints_force_zero (x : Fin 5 → ℝ) (s : Finset (Fin 10))
    (hs : s.card = 7) (he : ∀ e ∈ s, orderedEquation x e) : x 0 = 0 := by
  have hc := seven_candidates_complete s hs
  simp only [sevenCandidates, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 2 = x 0 + x 1 := he 9 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 2 = x 0 + x 1 := he 9 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h2 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 2 = x 0 + x 1 := he 9 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 2 = x 0 + x 1 := he 9 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 2 + x 3 := he 0 (by decide +kernel)
    have h1 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h2 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 2 = x 0 + x 1 := he 9 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h2 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 3 := he 1 (by decide +kernel)
    have h1 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h2 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 3 = x 0 + x 1 := he 8 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h1 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h2 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h3 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    have h4 : x 2 = x 0 + x 1 := he 9 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 4 = x 1 + x 2 := he 2 (by decide +kernel)
    have h1 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h2 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]
  ·
    have h0 : x 3 = x 1 + x 2 := he 3 (by decide +kernel)
    have h1 : x 4 = x 0 + x 3 := he 4 (by decide +kernel)
    have h2 : x 4 = x 0 + x 2 := he 5 (by decide +kernel)
    have h3 : x 3 = x 0 + x 2 := he 6 (by decide +kernel)
    have h4 : x 4 = x 0 + x 1 := he 7 (by decide +kernel)
    linarith only [h0, h1, h2, h3, h4]

end CentralConfigurations.FiveBody.RZero
