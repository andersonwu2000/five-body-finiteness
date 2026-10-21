import CentralConfigurations.Enumeration.ClosePairOrderDomains

/-!
# Certified finite-domain order comparisons

The four outputs distinguish strict smaller/larger order, two-sided
comparability, and lack of a certified comparison. An open level never
produces comparability solely because its two codes are equal.
-/

namespace CentralConfigurations

open Filter Asymptotics

inductive OrderComparison where
  | unknown | less | equal | greater
  deriving DecidableEq, Repr

def OrderComparison.Valid (c : OrderComparison) (f g : ℕ → ℂ) : Prop :=
  match c with
  | .unknown => True
  | .less => f =o[atTop] g
  | .equal => f =Θ[atTop] g
  | .greater => g =o[atTop] f

def OrderComparison.flip : OrderComparison → OrderComparison
  | .unknown => .unknown
  | .less => .greater
  | .equal => .equal
  | .greater => .less

theorem OrderComparison.Valid.flip {c : OrderComparison} {f g : ℕ → ℂ}
    (h : c.Valid f g) : c.flip.Valid g f := by
  cases c
  · trivial
  · exact h
  · exact h.symm
  · exact h

def compareOrderDomains (A B : Finset (Fin 6)) : OrderComparison :=
  if A.sup id < B.inf id then .less
  else if B.sup id < A.inf id then .greater
  else if ∃ k ∈ ({1, 3, 5} : Finset (Fin 6)), A = {k} ∧ B = {k} then .equal
  else .unknown

theorem compareOrderDomains_valid {s : OrderScales} {f g : ℕ → ℂ} {a b : Fin 6}
    (hf : HasOrderLevel s f a) (hg : HasOrderLevel s g b)
    (A B : Finset (Fin 6)) (ha : a ∈ A) (hb : b ∈ B) :
    (compareOrderDomains A B).Valid f g := by
  unfold compareOrderDomains
  split_ifs with hlt hgt heq
  · exact hf.littleO_of_lt hg
      ((Finset.le_sup (f := id) ha).trans_lt (hlt.trans_le (Finset.inf_le (f := id) hb)))
  · exact hg.littleO_of_lt hf
      ((Finset.le_sup (f := id) hb).trans_lt (hgt.trans_le (Finset.inf_le (f := id) ha)))
  · obtain ⟨k, hkp, hA, hB⟩ := heq
    have hak : a = k := by simpa [hA] using ha
    have hbk : b = k := by simpa [hB] using hb
    exact hf.isTheta_of_eq_precise hg (hak.trans hbk.symm) (hak ▸ hkp)
  · trivial

theorem isBigO_of_norm_triangle {f g h : ℕ → ℂ}
    (ht : ∀ t, ‖f t‖ ≤ ‖g t‖ + ‖h t‖) (hh : h =O[atTop] g) : f =O[atTop] g := by
  obtain ⟨C, _, hC⟩ := hh.exists_nonneg
  apply IsBigO.of_bound (1 + C)
  filter_upwards [hC.bound] with t hbound
  have htri := ht t
  nlinarith

theorem theta_of_norm_triangle_small_error {f g h : ℕ → ℂ}
    (hf : ∀ t, ‖f t‖ ≤ ‖g t‖ + ‖h t‖)
    (hg : ∀ t, ‖g t‖ ≤ ‖f t‖ + ‖h t‖) (hh : h =o[atTop] f) : f =Θ[atTop] g := by
  refine ⟨?_, isBigO_of_norm_triangle hg hh.isBigO⟩
  apply IsBigO.of_bound 2
  filter_upwards [(hh.forall_isBigOWith (by norm_num : (0 : ℝ) < 1 / 2)).bound] with t hbound
  have htri := hf t
  nlinarith

theorem HasOrderLevel.isBigO_across_precise {s : OrderScales} {f g : ℕ → ℂ}
    {a b c : Fin 6} (hf : HasOrderLevel s f a) (hg : HasOrderLevel s g b)
    (hac : a ≤ c) (hcb : c ≤ b) (hc : c ∈ ({1, 3, 5} : Finset (Fin 6))) :
    f =O[atTop] g := by
  rcases lt_or_eq_of_le hcb with hlt | rfl
  · exact (hf.littleO_of_lt hg (hac.trans_lt hlt)).isBigO
  · exact hg.isBigO_of_le_precise hf hac hc

def triangleDomainThetaCheck (A B C : Finset (Fin 6)) : Bool :=
  decide (C.sup id ≤ A.inf id ∧ C.sup id ≤ B.inf id ∧
    (C.sup id ∈ ({1, 3, 5} : Finset (Fin 6)) ∨ C.sup id < A.inf id ∨ C.sup id < B.inf id))

theorem triangleDomainThetaCheck_valid {s : OrderScales} {f g h : ℕ → ℂ}
    {a b c : Fin 6} (hf : HasOrderLevel s f a) (hg : HasOrderLevel s g b)
    (hh : HasOrderLevel s h c) (A B C : Finset (Fin 6))
    (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (htf : ∀ t, ‖f t‖ ≤ ‖g t‖ + ‖h t‖)
    (htg : ∀ t, ‖g t‖ ≤ ‖f t‖ + ‖h t‖)
    (hcheck : triangleDomainThetaCheck A B C = true) : f =Θ[atTop] g := by
  have hcheck' : C.sup id ≤ A.inf id ∧ C.sup id ≤ B.inf id ∧
      (C.sup id ∈ ({1, 3, 5} : Finset (Fin 6)) ∨ C.sup id < A.inf id ∨ C.sup id < B.inf id) :=
    of_decide_eq_true hcheck
  have hcs := Finset.le_sup (f := id) hc
  have has := Finset.inf_le (f := id) ha
  have hbs := Finset.inf_le (f := id) hb
  rcases hcheck'.2.2 with hp | hlt | hlt
  · exact ⟨isBigO_of_norm_triangle htf
        (hh.isBigO_across_precise hg hcs (hcheck'.2.1.trans hbs) hp),
      isBigO_of_norm_triangle htg
        (hh.isBigO_across_precise hf hcs (hcheck'.1.trans has) hp)⟩
  · exact theta_of_norm_triangle_small_error htf htg
      (hh.littleO_of_lt hf (hcs.trans_lt (hlt.trans_le has)))
  · exact (theta_of_norm_triangle_small_error htg htf
      (hh.littleO_of_lt hg (hcs.trans_lt (hlt.trans_le hbs)))).symm

end CentralConfigurations
