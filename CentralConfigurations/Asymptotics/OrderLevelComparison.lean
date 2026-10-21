import CentralConfigurations.Asymptotics.OrderLevelArithmetic

/-!
# Comparison and symmetry of the Section 4 levels

These lemmas transfer the analytic level semantics through the sign changes
in symmetric order matrices. They compare levels, not arbitrary growth rates
inside an open level.
-/

namespace CentralConfigurations

open Filter Asymptotics

theorem HasOrderLevel.of_isTheta {s : OrderScales} {f g : ℕ → ℂ} {k : Fin 6}
    (hf : HasOrderLevel s f k) (hfg : f =Θ[atTop] g) : HasOrderLevel s g k := by
  fin_cases k
  · exact hfg.symm.trans_isLittleO hf
  · exact hfg.symm.trans hf
  · exact ⟨hf.1.trans_isTheta hfg, hfg.symm.trans_isLittleO hf.2⟩
  · exact hfg.symm.trans hf
  · exact ⟨hf.1.trans_isTheta hfg, hfg.symm.trans_isLittleO hf.2⟩
  · exact hfg.symm.trans hf

theorem HasOrderLevel.congr_norm {s : OrderScales} {f g : ℕ → ℂ} {k : Fin 6}
    (hf : HasOrderLevel s f k) (hfg : ∀ t, ‖f t‖ = ‖g t‖) : HasOrderLevel s g k :=
  hf.of_isTheta (IsTheta.of_norm_eventuallyEq_norm (Eventually.of_forall hfg))

theorem HasOrderLevel.neg {s : OrderScales} {f : ℕ → ℂ} {k : Fin 6}
    (hf : HasOrderLevel s f k) : HasOrderLevel s (fun t => -f t) k :=
  hf.congr_norm (fun t => (norm_neg (f t)).symm)

theorem HasOrderLevel.one_iff_theta_lower {s : OrderScales} {f : ℕ → ℂ} {k : Fin 6}
    (hf : HasOrderLevel s f k) : k = 1 ↔ f =Θ[atTop] s.lower := by
  constructor
  · rintro rfl; exact hf
  · intro h; exact hf.unique (show HasOrderLevel s f 1 from h)

theorem HasOrderLevel.three_iff_theta_middle {s : OrderScales} {f : ℕ → ℂ} {k : Fin 6}
    (hf : HasOrderLevel s f k) : k = 3 ↔ f =Θ[atTop] s.middle := by
  constructor
  · rintro rfl; exact hf
  · intro h; exact hf.unique (show HasOrderLevel s f 3 from h)

theorem HasOrderLevel.le_of_isBigO {s : OrderScales} {f g : ℕ → ℂ} {k l : Fin 6}
    (hf : HasOrderLevel s f k) (hg : HasOrderLevel s g l) (hfg : f =O[atTop] g) : k ≤ l := by
  by_contra hn
  have hlt : l < k := lt_of_not_ge hn
  have ho : f =o[atTop] f := hfg.trans_isLittleO (hg.littleO_of_lt hf hlt)
  exact isLittleO_irrefl (hf.eventually_nonzero (by omega)).frequently ho

theorem HasOrderLevel.lt_three_iff_littleO_middle {s : OrderScales} {f : ℕ → ℂ}
    {k : Fin 6} (hf : HasOrderLevel s f k) : k < 3 ↔ f =o[atTop] s.middle := by
  have hm : HasOrderLevel s s.middle 3 := isTheta_rfl
  constructor
  · exact hf.littleO_of_lt hm
  · intro ho
    have hle := hf.le_of_isBigO hm ho.isBigO
    have hne : k ≠ 3 := by
      intro hk
      exact isLittleO_irrefl s.middle_nonzero.frequently
        ((hf.three_iff_theta_middle.mp hk).symm.trans_isLittleO ho)
    exact lt_of_le_of_ne hle hne

theorem HasOrderLevel.three_lt_iff_middle_littleO {s : OrderScales} {f : ℕ → ℂ}
    {k : Fin 6} (hf : HasOrderLevel s f k) : 3 < k ↔ s.middle =o[atTop] f := by
  have hm : HasOrderLevel s s.middle 3 := isTheta_rfl
  constructor
  · exact hm.littleO_of_lt hf
  · intro ho
    have hle := hm.le_of_isBigO hf ho.isBigO
    have hne : (3 : Fin 6) ≠ k := by
      intro hk
      exact isLittleO_irrefl s.middle_nonzero.frequently
        (ho.trans_isTheta (hf.three_iff_theta_middle.mp hk.symm))
    exact lt_of_le_of_ne hle hne

theorem HasOrderLevel.le_three_iff_isBigO_middle {s : OrderScales} {f : ℕ → ℂ}
    {k : Fin 6} (hf : HasOrderLevel s f k) : k ≤ 3 ↔ f =O[atTop] s.middle := by
  have hm : HasOrderLevel s s.middle 3 := isTheta_rfl
  constructor
  · intro hk
    rcases lt_or_eq_of_le hk with hk | hk
    · exact (hf.littleO_of_lt hm hk).isBigO
    · exact (hf.three_iff_theta_middle.mp hk).1
  · exact hf.le_of_isBigO hm

end CentralConfigurations
