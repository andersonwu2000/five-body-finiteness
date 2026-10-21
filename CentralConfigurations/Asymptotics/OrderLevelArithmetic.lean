import CentralConfigurations.Asymptotics.OrderLevels

/-!
# Strict order levels and the triangle restriction

Different levels are strictly ordered even though two variables within an
open level need not be comparable. This proves uniqueness of the level and
the no-unique-largest-term principle used in Proposition 4.5.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

theorem HasOrderLevel.lower_isBigO_of_ne_zero {s : OrderScales} {f : ℕ → ℂ}
    {k : Fin 6} (h : HasOrderLevel s f k) (hk : k ≠ 0) : s.lower =O[atTop] f := by
  fin_cases k <;> dsimp only at *
  · exact (hk rfl).elim
  · exact h.2
  · exact h.1.isBigO
  · exact s.lower_middle.isBigO.trans h.2
  · exact s.lower_middle.isBigO.trans h.1.isBigO
  · exact s.lower_upper.isBigO.trans h.2

theorem HasOrderLevel.lower_littleO_of_one_lt {s : OrderScales} {f : ℕ → ℂ}
    {k : Fin 6} (h : HasOrderLevel s f k) (hk : 1 < k) : s.lower =o[atTop] f := by
  have hkNat : 1 < k.val := hk
  fin_cases k <;> dsimp only at *
  · omega
  · omega
  · exact h.1
  · exact s.lower_middle.trans_isBigO h.2
  · exact s.lower_middle.trans h.1
  · exact s.lower_upper.trans_isBigO h.2

theorem HasOrderLevel.middle_isBigO_of_three_le {s : OrderScales} {f : ℕ → ℂ}
    {k : Fin 6} (h : HasOrderLevel s f k) (hk : 3 ≤ k) : s.middle =O[atTop] f := by
  have hkNat : 3 ≤ k.val := hk
  fin_cases k <;> dsimp only at *
  · omega
  · omega
  · omega
  · exact h.2
  · exact h.1.isBigO
  · exact s.middle_upper.isBigO.trans h.2

theorem HasOrderLevel.middle_littleO_of_three_lt {s : OrderScales} {f : ℕ → ℂ}
    {k : Fin 6} (h : HasOrderLevel s f k) (hk : 3 < k) : s.middle =o[atTop] f := by
  have hkNat : 3 < k.val := hk
  fin_cases k <;> dsimp only at *
  · omega
  · omega
  · omega
  · omega
  · exact h.1
  · exact s.middle_upper.trans_isBigO h.2

theorem HasOrderLevel.eventually_nonzero {s : OrderScales} {f : ℕ → ℂ}
    {k : Fin 6} (h : HasOrderLevel s f k) (hk : k ≠ 0) :
    ∀ᶠ t in atTop, f t ≠ 0 := by
  filter_upwards [(h.lower_isBigO_of_ne_zero hk).eq_zero_imp, s.lower_nonzero] with t ht hn
  exact fun hf => hn (ht hf)

theorem HasOrderLevel.littleO_of_lt {s : OrderScales} {f g : ℕ → ℂ}
    {k l : Fin 6} (hf : HasOrderLevel s f k) (hg : HasOrderLevel s g l)
    (hkl : k < l) : f =o[atTop] g := by
  have hklNat : k.val < l.val := hkl
  fin_cases k <;> dsimp only at *
  · exact hf.trans_isBigO (hg.lower_isBigO_of_ne_zero (by omega))
  · exact hf.trans_isLittleO (hg.lower_littleO_of_one_lt hkl)
  · exact hf.2.trans_isBigO (hg.middle_isBigO_of_three_le (by omega))
  · exact hf.trans_isLittleO (hg.middle_littleO_of_three_lt hkl)
  · have hl : l = 5 := by apply Fin.ext; omega
    subst l
    exact hf.2.trans_isBigO hg.2
  · omega

theorem HasOrderLevel.unique {s : OrderScales} {f : ℕ → ℂ} {k l : Fin 6}
    (hk : HasOrderLevel s f k) (hl : HasOrderLevel s f l) : k = l := by
  rcases lt_trichotomy k l with h | h | h
  · exact (isLittleO_irrefl (hl.eventually_nonzero (by omega)).frequently
      (hk.littleO_of_lt hl h)).elim
  · exact h
  · exact (isLittleO_irrefl (hk.eventually_nonzero (by omega)).frequently
      (hl.littleO_of_lt hk h)).elim

theorem HasOrderLevel.le_max_of_add {s : OrderScales} {f g h : ℕ → ℂ}
    {kf kg kh : Fin 6} (hf : HasOrderLevel s f kf)
    (hg : HasOrderLevel s g kg) (hh : HasOrderLevel s h kh)
    (heq : ∀ t, f t = g t + h t) : kf ≤ max kg kh := by
  by_contra hn
  have hfg : kg < kf := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge hn)
  have hfh : kh < kf := lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge hn)
  have ho := (hg.littleO_of_lt hf hfg).add (hh.littleO_of_lt hf hfh)
  apply isLittleO_irrefl (hf.eventually_nonzero (by omega)).frequently
  exact ho.congr (fun t => (heq t).symm) (fun _ => rfl)

end CentralConfigurations
