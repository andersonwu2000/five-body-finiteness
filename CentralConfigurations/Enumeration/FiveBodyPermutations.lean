import CentralConfigurations.Enumeration.MonochromeWitnesses

/-! Complete fixed-width permutation codes for the five-body certificate. -/
namespace CentralConfigurations.FiveBodyPermutations

def encode (e : Fin 5 → Fin 5) : ℕ :=
  (e 0).val + 5*(e 1).val + 25*(e 2).val + 125*(e 3).val + 625*(e 4).val

def decode (v : ℕ) (i : Fin 5) : Fin 5 :=
  ⟨v / 5^i.val % 5, Nat.mod_lt _ (by decide)⟩

theorem decode_encode (e : Fin 5 → Fin 5) : decode (encode e) = e := by
  funext i
  apply Fin.ext
  have h0 := (e 0).isLt
  have h1 := (e 1).isLt
  have h2 := (e 2).isLt
  have h3 := (e 3).isLt
  have h4 := (e 4).isLt
  fin_cases i
  · change encode e / 1 % 5 = (e 0).val; unfold encode; omega
  · change encode e / 5 % 5 = (e 1).val; unfold encode; omega
  · change encode e / 25 % 5 = (e 2).val; unfold encode; omega
  · change encode e / 125 % 5 = (e 3).val; unfold encode; omega
  · change encode e / 625 % 5 = (e 4).val; unfold encode; omega

def generated : List ℕ := (permsOfList (List.finRange 5)).map
  (fun (e : Equiv.Perm (Fin 5)) => encode e)

theorem generated_covers (e : Equiv.Perm (Fin 5)) :
    ∃ v ∈ generated, decode v = e := by
  refine ⟨encode e, ?_, decode_encode e⟩
  apply List.mem_map.mpr
  exact ⟨e, mem_permsOfList_of_mem (fun x _ => List.mem_finRange x), rfl⟩

end CentralConfigurations.FiveBodyPermutations
