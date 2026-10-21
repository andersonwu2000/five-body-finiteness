import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fin.Tuple.Sort

/-!
# Finite codes for symmetric binary matrices

Only upper-triangular entries are stored. Decoding and encoding are inverse
on symmetric binary matrices. Relabeling uses the same permutation for both
matrix indices. The diagonal-prefix generator is the reduction in (6.1),
before applying trace and monochrome filters.
-/

namespace CentralConfigurations

abbrev UpperIndex (n : ℕ) := {p : Fin n × Fin n // p.1 ≤ p.2}
abbrev StrictUpperIndex (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}
abbrev BinaryMatrixCode (n : ℕ) := UpperIndex n → Bool

def upperIndex {n : ℕ} (i j : Fin n) : UpperIndex n :=
  ⟨(min i j, max i j), min_le_max⟩

theorem upperIndex_symm {n : ℕ} (i j : Fin n) : upperIndex i j = upperIndex j i := by
  simp [upperIndex, min_comm, max_comm]

theorem upperIndex_of_le {n : ℕ} (p : UpperIndex n) : upperIndex p.1.1 p.1.2 = p := by
  apply Subtype.ext
  simp [upperIndex, min_eq_left p.2, max_eq_right p.2]

namespace BinaryMatrixCode

def decode {n : ℕ} (c : BinaryMatrixCode n) (i j : Fin n) : ℕ :=
  if c (upperIndex i j) then 1 else 0

def encode {n : ℕ} (A : Fin n → Fin n → ℕ) : BinaryMatrixCode n :=
  fun p => decide (A p.1.1 p.1.2 = 1)

theorem decode_binary {n : ℕ} (c : BinaryMatrixCode n) (i j : Fin n) :
    decode c i j = 0 ∨ decode c i j = 1 := by
  unfold decode
  split <;> simp_all

theorem decode_symm {n : ℕ} (c : BinaryMatrixCode n) (i j : Fin n) :
    decode c i j = decode c j i := by rw [decode, decode, upperIndex_symm]

@[simp] theorem decode_upper {n : ℕ} (c : BinaryMatrixCode n) (p : UpperIndex n) :
    decode c p.1.1 p.1.2 = if c p then 1 else 0 := by
  simp only [decode, upperIndex_of_le]

@[simp] theorem encode_decode {n : ℕ} (c : BinaryMatrixCode n) : encode (decode c) = c := by
  funext p
  simp only [encode, decode_upper]
  cases c p <;> rfl

theorem decode_encode {n : ℕ} (A : Fin n → Fin n → ℕ)
    (hb : ∀ i j, A i j = 0 ∨ A i j = 1) (hs : ∀ i j, A i j = A j i) :
    decode (encode A) = A := by
  funext i j
  by_cases hij : i ≤ j
  · rcases hb i j with h | h <;>
      simp [decode, encode, upperIndex, min_eq_left hij, max_eq_right hij, h]
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    rcases hb j i with h | h <;>
      simp [decode, encode, upperIndex, min_eq_right hji, max_eq_left hji, hs i j, h]

theorem decode_injective {n : ℕ} : Function.Injective (@decode n) := by
  intro c d h
  simpa only [encode_decode] using congrArg encode h

def relabel {n : ℕ} (c : BinaryMatrixCode n) (e : Equiv.Perm (Fin n)) : BinaryMatrixCode n :=
  encode (fun i j => decode c (e i) (e j))

@[simp] theorem decode_relabel {n : ℕ} (c : BinaryMatrixCode n) (e : Equiv.Perm (Fin n)) :
    decode (relabel c e) = fun i j => decode c (e i) (e j) :=
  decode_encode _ (fun i j => decode_binary c (e i) (e j))
    (fun i j => decode_symm c (e i) (e j))

@[simp] theorem relabel_refl {n : ℕ} (c : BinaryMatrixCode n) :
    relabel c (Equiv.refl _) = c := by
  apply decode_injective
  simp

theorem relabel_relabel {n : ℕ} (c : BinaryMatrixCode n) (e f : Equiv.Perm (Fin n)) :
    relabel (relabel c e) f = relabel c (f.trans e) := by
  apply decode_injective
  simp [Equiv.trans_apply]

@[simp] theorem relabel_inverse {n : ℕ} (c : BinaryMatrixCode n) (e : Equiv.Perm (Fin n)) :
    relabel (relabel c e) e.symm = c := by
  apply decode_injective
  simp

def sortDiagonal {n : ℕ} (c : BinaryMatrixCode n) : Equiv.Perm (Fin n) :=
  Tuple.sort (fun i => decode c i i)

theorem sorted_diagonal {n : ℕ} (c : BinaryMatrixCode n) :
    Monotone (fun i => decode (relabel c (sortDiagonal c)) i i) := by
  simpa only [decode_relabel, sortDiagonal, Function.comp_def] using
    Tuple.monotone_sort (fun i => decode c i i)

/-- `cut` is the number of initial zero diagonal entries. -/
def withZeroPrefix {n : ℕ} (cut : Fin (n + 1)) (edges : StrictUpperIndex n → Bool) :
    BinaryMatrixCode n := fun p =>
  if h : p.1.1 = p.1.2 then decide (cut.val ≤ p.1.1.val)
  else edges ⟨p.1, lt_of_le_of_ne p.2 h⟩

def offDiagonal {n : ℕ} (c : BinaryMatrixCode n) : StrictUpperIndex n → Bool :=
  fun p => c ⟨p.1, p.2.le⟩

def zeroCut {n : ℕ} (c : BinaryMatrixCode n) : Fin (n + 1) :=
  ⟨(Finset.univ.filter (fun i => decode c i i = 0)).card, by
    have h := Finset.card_le_card (Finset.filter_subset (fun i => decode c i i = 0) Finset.univ)
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega⟩

/-- Every sorted binary diagonal has exactly the threshold shape used in (6.1). -/
theorem prefix_zeroCut {n : ℕ} (c : BinaryMatrixCode n)
    (hm : Monotone (fun i => decode c i i)) : withZeroPrefix (zeroCut c) (offDiagonal c) = c := by
  funext p
  by_cases he : p.1.1 = p.1.2
  · have h := Tuple.lt_card_le_iff_apply_le_of_monotone (j := p.1.1) (a := 0) hm
    simp only [Nat.le_zero] at h
    have hd : decode c p.1.1 p.1.1 = if c p then 1 else 0 := by
      simpa only [← he] using decode_upper c p
    simp only [withZeroPrefix, dif_pos he, zeroCut]
    cases hp : c p <;> simp [hp] at hd ⊢
    · have hh := h.mpr hd
      omega
    · have hh : ¬ p.1.1.val < (Finset.univ.filter (fun i => decode c i i = 0)).card := by
        intro hx
        have := h.mp hx
        omega
      omega
  · simp [withZeroPrefix, he, offDiagonal]

theorem withZeroPrefix_injective {n : ℕ} : Function.Injective
    (fun p : Fin (n + 1) × (StrictUpperIndex n → Bool) => withZeroPrefix p.1 p.2) := by
  rintro ⟨c, a⟩ ⟨d, b⟩ h
  have hcut : c = d := by
    apply Fin.ext
    by_contra hv
    rcases lt_or_gt_of_ne hv with hlt | hgt
    · let i : Fin n := ⟨c.val, by omega⟩
      have hi := congrFun h (upperIndex i i)
      have hd : ¬ d.val ≤ c.val := by omega
      simp [withZeroPrefix, upperIndex, i, hd] at hi
    · let i : Fin n := ⟨d.val, by omega⟩
      have hi := congrFun h (upperIndex i i)
      have hc : ¬ c.val ≤ d.val := by omega
      simp [withZeroPrefix, upperIndex, i, hc] at hi
  have hab : a = b := by
    funext p
    have hp := congrFun h (⟨p.1, p.2.le⟩ : UpperIndex n)
    simpa only [withZeroPrefix, dif_neg (ne_of_lt p.2)] using hp
  cases hcut
  cases hab
  rfl

/-- Injectivity avoids quadratic duplicate removal in the raw generator. -/
def prefixEmbedding (n : ℕ) :
    (Fin (n + 1) × (StrictUpperIndex n → Bool)) ↪ BinaryMatrixCode n :=
  ⟨fun p => withZeroPrefix p.1 p.2, withZeroPrefix_injective⟩

/-- The source's diagonal-normalized raw candidates, before rejecting trace one. -/
def prefixCandidates (n : ℕ) : Finset (BinaryMatrixCode n) :=
  Finset.univ.map (prefixEmbedding n)

theorem normalized_mem_prefixCandidates {n : ℕ} (c : BinaryMatrixCode n) :
    relabel c (sortDiagonal c) ∈ prefixCandidates n := by
  apply Finset.mem_map.mpr
  exact ⟨(zeroCut (relabel c (sortDiagonal c)), offDiagonal (relabel c (sortDiagonal c))),
    Finset.mem_univ _, prefix_zeroCut _ (sorted_diagonal c)⟩

end BinaryMatrixCode

end CentralConfigurations
