import CentralConfigurations.Enumeration.FiveBodyRaw

/-!
# Five-body coverage certificate checker

Each packed entry supplies either one failed original rule, or a representative
index and a concrete permutation. The soundness theorem proves that every accepted witness establishes the
required alternative. External candidate generation supplies data only.
-/

namespace CentralConfigurations.FiveBodyMono

set_option maxRecDepth 10000

open BinaryMatrixCode

def representativeMasks : Array Nat := #[70, 204, 476, 1230, 1310, 1368, 1370, 11742, 21055, 21113, 21115, 21119, 21237, 21239, 21245, 21472, 21478, 21501, 22098, 22226, 22257, 22259, 22271, 22290, 22304, 22316, 22335, 22368, 22374, 22380, 22393, 22395, 22496, 22510, 22514, 24064, 24076, 24202, 24210, 24214, 24270, 24480, 24490, 28672, 28696, 28742, 28766, 29082, 32222, 32256, 32284, 32734, 32736, 32766, 32767]

def representatives : Finset (BinaryMatrixCode 5) :=
  representativeMasks.toList.toFinset.image (fromMask 5)

def digit (v k : ℕ) : Fin 5 := ⟨v / 5 ^ k % 5, Nat.mod_lt _ (by decide)⟩

def rejection (w : ℕ) : MonoRejection 5 :=
  let v := w / 16
  match w % 16 with
  | 0 => .column (digit v 0)
  | 1 => .zero
  | 2 => .traceOne
  | 3 => .traceTwo (digit v 0) (digit v 1)
  | 4 => .triangle (digit v 0) (digit v 1) (digit v 2)
  | 5 => .quadrilateral (digit v 0) (digit v 1) (digit v 2) (digit v 3)
  | 6 => .traceThree (digit v 0) (digit v 1) (digit v 2) (digit v 3)
  | 7 => .cut (Finset.univ.filter (fun i => v.testBit i.val = true))
  | _ => .zero

def witnessCheck (i w : ℕ) : Bool :=
  let c := FiveBodyRaw.atIndex i
  if w % 16 = 8 then
    let r := w / 16 / 3125
    if h : r < representativeMasks.size then
      decide (monoOrbitWitness c (fromMask 5 representativeMasks[r])
        (fun j => digit (w / 16 % 3125) j.val))
    else false
  else decide ((rejection w).holds (decode c))

def Covered (i : ℕ) : Prop :=
  MonochromeConditions (decode (FiveBodyRaw.atIndex i)) →
    ∃ r ∈ representatives, ∃ e : Equiv.Perm (Fin 5),
      relabel (FiveBodyRaw.atIndex i) e = r

theorem witnessCheck_sound (i w : ℕ) (h : witnessCheck i w = true) : Covered i := by
  intro hc
  dsimp only [witnessCheck] at h
  split_ifs at h with htag hidx
  · refine ⟨fromMask 5 representativeMasks[w / 16 / 3125], ?_,
      monoOrbitWitness_sound (of_decide_eq_true h)⟩
    apply Finset.mem_image.mpr
    exact ⟨_, List.mem_toFinset.mpr (Array.getElem_mem_toList hidx), rfl⟩
  · exact ((rejection w).excludes (of_decide_eq_true h) hc).elim

theorem block_sound (start : ℕ) (ws : List ℕ)
    (h : consecutiveCheck witnessCheck start ws = true) :
    ∀ i, start ≤ i → i < start + ws.length → Covered i :=
  consecutiveCheck_sound witnessCheck_sound start ws h

theorem coverage_of_raw_covered (h : ∀ i, i < 6144 → Covered i) :
    MonochromeCovers representatives := by
  intro c hc
  obtain ⟨hp, hm⟩ := Finset.mem_filter.mp hc
  obtain ⟨i, hi, he⟩ := FiveBodyRaw.prefix_mem_index hp
  have hh := h i hi
  unfold Covered at hh
  rw [he] at hh
  exact hh ((monochromeCheck_eq_true c).mp hm)

end CentralConfigurations.FiveBodyMono
