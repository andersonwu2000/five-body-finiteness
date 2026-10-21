import CentralConfigurations.Enumeration.FiveBodyPairData
import CentralConfigurations.Enumeration.FiveBodyMonoCheck
import CentralConfigurations.Enumeration.OrbitMatching

/-!
# Certified coarse reduction before enumerating pair labelings

Trace order and the connected-companion rule reject whole pairs of monochrome
representatives, independently of their relative labeling. The surviving rows
are certified finite data, not a sampling of the pair space.
-/

namespace CentralConfigurations.FiveBodyPairs

open BinaryMatrixCode

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def rep (i : Fin 55) : BinaryMatrixCode 5 :=
  fromMask 5 (FiveBodyMono.representativeMasks[i.val]'(by exact i.isLt))

theorem traces_checked : ∀ i : Fin 55, trace (rep i) = traces[i.val] := by decide +kernel

theorem connectivity_checked : ∀ i : Fin 55,
    connectedFlags[i.val] = true → ConnectedCuts (decode (rep i)) := by decide +kernel

theorem connected_sound (i : Fin 55) (hi : connectedFlags[i.val] = true) :
    AlgorithmFullyConnected (decode (rep i)) :=
  (connectivity_checked i hi).algorithmFullyConnected (decode_symm _)

theorem permutation_codes_checked : permutationCodes.toList = FiveBodyPermutations.generated := by
  decide +kernel

theorem permutations_cover (e : Equiv.Perm (Fin 5)) :
    ∃ v ∈ permutationCodes.toList, FiveBodyPermutations.decode v = e := by
  rw [permutation_codes_checked]
  exact FiveBodyPermutations.generated_covers e

def coarseReject (a b : Fin 55) : Bool :=
  decide (traces[b.val] < traces[a.val]) ||
  (connectedFlags[a.val] && decide (traces[b.val] ≠ 0)) ||
  (connectedFlags[b.val] && decide (traces[a.val] ≠ 0))

theorem coarse_rejects (a b : Fin 55) (e : Equiv.Perm (Fin 5))
    (h : coarseReject a b = true) :
    ¬ (trace (rep a) ≤ trace (relabel (rep b) e) ∧
      BicoloredConditions (decode (rep a)) (decode (relabel (rep b) e))) := by
  rintro ⟨horder, hc⟩
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hA, hB, _, _, _⟩ := hc
  simp only [coarseReject, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rw [trace_relabel, traces_checked, traces_checked] at horder
  rcases h with (h | h) | h
  · omega
  · have hz := hA (connected_sound a h.1)
    change trace (relabel (rep b) e) = 0 at hz
    rw [trace_relabel, traces_checked] at hz
    exact h.2 hz
  · have hh : AlgorithmFullyConnected (decode (relabel (rep b) e)) := by
      simpa only [decode_relabel] using (connected_sound b h.1).relabel e
    have hz := hB hh
    change trace (rep a) = 0 at hz
    rw [traces_checked] at hz
    exact h.2 hz

theorem surviving_rows_checked : ∀ a b : Fin 55,
    b.val ∈ (survivingRows[a.val]).toList ↔ coarseReject a b = false := by decide +kernel

theorem surviving_rows_bounded : ∀ a : Fin 55,
    ∀ b ∈ (survivingRows[a.val]).toList, b < 55 := by decide +kernel

theorem surviving_rows_count :
    (survivingRows.toList.map (fun row => row.size)).sum = 414 := by decide +kernel

theorem permutation_count : permutationCodes.size = 120 := by rfl

theorem admissible_pair_survives (a b : Fin 55) (e : Equiv.Perm (Fin 5))
    (horder : trace (rep a) ≤ trace (relabel (rep b) e))
    (hc : BicoloredConditions (decode (rep a)) (decode (relabel (rep b) e))) :
    b.val ∈ (survivingRows[a.val]).toList := by
  apply (surviving_rows_checked a b).mpr
  cases he : coarseReject a b with
  | false => rfl
  | true => exact (coarse_rejects a b e he ⟨horder, hc⟩).elim

theorem mem_representatives_iff (c : BinaryMatrixCode 5) :
    c ∈ FiveBodyMono.representatives ↔ ∃ i : Fin 55, rep i = c := by
  constructor
  · intro hc
    obtain ⟨mask, hm, he⟩ := Finset.mem_image.mp hc
    have hma : mask ∈ FiveBodyMono.representativeMasks :=
      Array.mem_toList_iff.mp (List.mem_toFinset.mp hm)
    obtain ⟨i, hi, hmask⟩ := Array.getElem_of_mem hma
    refine ⟨⟨i, hi⟩, ?_⟩
    change fromMask 5 FiveBodyMono.representativeMasks[i] = c
    rw [hmask]
    exact he
  · rintro ⟨i, rfl⟩
    exact Finset.mem_image.mpr ⟨_, List.mem_toFinset.mpr
      (Array.getElem_mem_toList i.isLt), rfl⟩

end CentralConfigurations.FiveBodyPairs
