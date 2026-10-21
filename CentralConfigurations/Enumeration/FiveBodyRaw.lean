import CentralConfigurations.Enumeration.MonochromeWitnesses

/-!
# Exhaustive integer indexing of the five-body raw search space

Six diagonal cuts and ten independent edge bits give 6144 inputs.
The coverage theorem is for arbitrary binary edge functions, not just for
the masks output by an external generator.
-/

namespace CentralConfigurations.FiveBodyRaw

open BinaryMatrixCode

def edgeIndex (p : StrictUpperIndex 5) : ℕ :=
  p.1.1.val * (9 - p.1.1.val) / 2 + (p.1.2.val - p.1.1.val - 1)

theorem edgeIndex_lt : ∀ p : StrictUpperIndex 5, edgeIndex p < 10 := by decide

def edgeFin (p : StrictUpperIndex 5) : Fin 10 := ⟨edgeIndex p, edgeIndex_lt p⟩

theorem edgeFin_bijective : Function.Bijective edgeFin := by decide

noncomputable def edgeEquiv : StrictUpperIndex 5 ≃ Fin 10 :=
  Equiv.ofBijective edgeFin edgeFin_bijective

def code (cut : Fin 6) (mask : ℕ) : BinaryMatrixCode 5 :=
  withZeroPrefix cut (fun p => mask.testBit (edgeIndex p))

theorem edges_representable (edges : StrictUpperIndex 5 → Bool) :
    ∃ mask < 1024, ∀ p, mask.testBit (edgeIndex p) = edges p := by
  let bs := List.ofFn (fun i : Fin 10 => edges (edgeEquiv.symm i))
  let v := BitVec.ofBoolListLE bs
  refine ⟨v.toNat, ?_, ?_⟩
  · have h := v.isLt
    simpa [v, bs] using h
  · intro p
    change v.getLsbD (edgeIndex p) = edges p
    simp only [v, BitVec.getLsbD_ofBoolListLE, bs, List.getD_eq_getElem?_getD,
      List.getElem?_ofFn, dif_pos (edgeIndex_lt p), Option.getD_some]
    change edges (edgeEquiv.symm (edgeEquiv p)) = edges p
    rw [Equiv.symm_apply_apply]

theorem prefix_representable (cut : Fin 6) (edges : StrictUpperIndex 5 → Bool) :
    ∃ mask < 1024, code cut mask = withZeroPrefix cut edges := by
  obtain ⟨mask, hm, he⟩ := edges_representable edges
  exact ⟨mask, hm, congrArg (withZeroPrefix cut) (funext he)⟩

def atIndex (i : ℕ) : BinaryMatrixCode 5 :=
  code ⟨i / 1024 % 6, Nat.mod_lt _ (by decide)⟩ (i % 1024)

theorem prefix_mem_index {c : BinaryMatrixCode 5} (hc : c ∈ prefixCandidates 5) :
    ∃ i < 6144, atIndex i = c := by
  obtain ⟨⟨cut, edges⟩, _, h⟩ := Finset.mem_map.mp hc
  obtain ⟨mask, hm, he⟩ := prefix_representable cut edges
  refine ⟨cut.val * 1024 + mask, by have := cut.isLt; omega, ?_⟩
  have hdiv : (cut.val * 1024 + mask) / 1024 % 6 = cut.val := by omega
  have hmod : (cut.val * 1024 + mask) % 1024 = mask := by omega
  have hfin : (⟨(cut.val * 1024 + mask) / 1024 % 6,
      Nat.mod_lt _ (by decide)⟩ : Fin 6) = cut := Fin.ext hdiv
  simpa only [atIndex, hmod, hfin, he, prefixEmbedding, Function.Embedding.coeFn_mk] using h

end CentralConfigurations.FiveBodyRaw
