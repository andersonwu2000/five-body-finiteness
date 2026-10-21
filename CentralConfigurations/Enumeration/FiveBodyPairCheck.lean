import CentralConfigurations.Enumeration.FiveBodyPairCoarse
import CentralConfigurations.Enumeration.FiveBodySourceData
import CentralConfigurations.Enumeration.PairWitnesses

/-!
# Local witnesses covering all five-body relative labelings

Each input is either rejected by one proved Appendix-I rule, or transported
to one of the actual twenty source masks by a common vertex permutation.
-/

namespace CentralConfigurations.FiveBodyPairs
open BinaryMatrixCode
set_option maxRecDepth 20000
set_option maxHeartbeats 0
attribute [local irreducible] DiagramCode.orbit

def witnessDigit (v k : ℕ) : Fin 5 := ⟨v / 5^k % 5, Nat.mod_lt _ (by decide)⟩

def pairRejection (w : ℕ) : PairRejection 5 :=
  let v := w/32
  let i := witnessDigit v 0
  let j := witnessDigit v 1
  let k := witnessDigit v 2
  let r := witnessDigit v 3
  match w%32 with
  | 0 => .oriented false (.circling i j)
  | 1 => .oriented true (.circling i j)
  | 2 => .oriented false (.traceRows i j k)
  | 3 => .oriented true (.traceRows i j k)
  | 4 => .oriented false (.positiveTrace i j)
  | 5 => .oriented true (.positiveTrace i j)
  | 6 => .oriented false .component
  | 7 => .oriented true .component
  | 8 => .oriented false (.star i j k)
  | 9 => .oriented true (.star i j k)
  | 10 => .triangle i j k
  | 11 => .columns i j
  | 12 => .quadrilateral i j k r
  | 13 => .pentagon (fun t => witnessDigit v t.val)
  | 14 => .secondTrace
  | _ => .singleDouble

def pairWitnessCheck (d : DiagramCode 5) (w : ℕ) : Bool :=
  if w%32 = 16 then
    let r := w/32/2/3125
    if h : r < 20 then
      decide (PairOrbitWitness d (fiveBodySourceDiagram ⟨r,h⟩)
        (FiveBodyPermutations.decode (w/32/2%3125)) (decide (w/32%2=1)))
    else false
  else decide ((pairRejection w).holds (decode d.1) (decode d.2))

theorem pairWitnessCheck_sound (d : DiagramCode 5) (w : ℕ)
    (hw : pairWitnessCheck d w = true) (hc : appendixCandidateCheck d.1 d.2 = true) :
    ∃ k : Fin 20, fiveBodySourceDiagram k ∈ DiagramCode.orbit d := by
  dsimp only [pairWitnessCheck] at hw
  split_ifs at hw with htag hr
  · exact ⟨⟨w/32/2/3125,hr⟩, PairOrbitWitness.sound (of_decide_eq_true hw)⟩
  · exact ((pairRejection w).excludes_check (of_decide_eq_true hw) hc).elim

def inputPair (a b : Fin 55) (k : Fin 120) : DiagramCode 5 :=
  (rep a, rawRelabel (rep b) (FiveBodyPermutations.decode
    (permutationCodes[k.val]'(by exact k.isLt))))

def rowCheck (a b : Fin 55) (k w : ℕ) : Bool :=
  if hk : k < 120 then pairWitnessCheck (inputPair a b ⟨k,hk⟩) w else false

def RowCovered (a b : Fin 55) (k : ℕ) : Prop :=
  ∀ hk : k < 120,
    appendixCandidateCheck (inputPair a b ⟨k,hk⟩).1 (inputPair a b ⟨k,hk⟩).2 = true →
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair a b ⟨k,hk⟩)

theorem rowCheck_sound (a b : Fin 55) (k w : ℕ) (h : rowCheck a b k w = true) :
    RowCovered a b k := by
  intro hk hc
  simp only [rowCheck, dif_pos hk] at h
  exact pairWitnessCheck_sound _ w h hc

theorem row_coverage_of_check (a b : Fin 55) (ws : List ℕ) (hlen : ws.length = 120)
    (h : consecutiveCheck (rowCheck a b) 0 ws = true) (k : Fin 120)
    (hc : appendixCandidateCheck (inputPair a b k).1 (inputPair a b k).2 = true) :
    ∃ r : Fin 20, fiveBodySourceDiagram r ∈ DiagramCode.orbit (inputPair a b k) := by
  have hk : k.val < 0+ws.length := by rw [hlen]; exact k.isLt
  exact consecutiveCheck_sound (rowCheck_sound a b) 0 ws h k.val (Nat.zero_le _) hk k.isLt hc

end CentralConfigurations.FiveBodyPairs
