import CentralConfigurations.Asymptotics.OrderTrichotomy

/-!
# Six discrete order levels

The thresholds in Section 4 are three separated scales. Levels 0, 2, and 4
are open ranges, not assumed power laws. Levels 1, 3, and 5 mean two-sided
comparability. A common subsequence assigns a level to every variable in a
finite family bounded above by the largest scale. A lower bound excludes
level 0 for separations (or distances with their different thresholds).
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

structure OrderScales where
  lower : ℕ → ℂ
  middle : ℕ → ℂ
  upper : ℕ → ℂ
  lower_nonzero : ∀ᶠ t in atTop, lower t ≠ 0
  middle_nonzero : ∀ᶠ t in atTop, middle t ≠ 0
  upper_nonzero : ∀ᶠ t in atTop, upper t ≠ 0
  lower_middle : lower =o[atTop] middle
  middle_upper : middle =o[atTop] upper

namespace OrderScales

def comp (s : OrderScales) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) : OrderScales where
  lower := s.lower ∘ φ
  middle := s.middle ∘ φ
  upper := s.upper ∘ φ
  lower_nonzero := hφ.eventually s.lower_nonzero
  middle_nonzero := hφ.eventually s.middle_nonzero
  upper_nonzero := hφ.eventually s.upper_nonzero
  lower_middle := s.lower_middle.comp_tendsto hφ
  middle_upper := s.middle_upper.comp_tendsto hφ

theorem lower_upper (s : OrderScales) : s.lower =o[atTop] s.upper :=
  s.lower_middle.trans s.middle_upper

end OrderScales

def HasOrderLevel (s : OrderScales) (f : ℕ → ℂ) (k : Fin 6) : Prop :=
  match k.val with
  | 0 => f =o[atTop] s.lower
  | 1 => f =Θ[atTop] s.lower
  | 2 => s.lower =o[atTop] f ∧ f =o[atTop] s.middle
  | 3 => f =Θ[atTop] s.middle
  | 4 => s.middle =o[atTop] f ∧ f =o[atTop] s.upper
  | _ => f =Θ[atTop] s.upper

theorem HasOrderLevel.comp {s : OrderScales} {f : ℕ → ℂ} {k : Fin 6}
    (h : HasOrderLevel s f k) (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    HasOrderLevel (s.comp φ hφ) (f ∘ φ) k := by
  fin_cases k
  · exact h.comp_tendsto hφ
  · exact ⟨h.1.comp_tendsto hφ, h.2.comp_tendsto hφ⟩
  · exact ⟨h.1.comp_tendsto hφ, h.2.comp_tendsto hφ⟩
  · exact ⟨h.1.comp_tendsto hφ, h.2.comp_tendsto hφ⟩
  · exact ⟨h.1.comp_tendsto hφ, h.2.comp_tendsto hφ⟩
  · exact ⟨h.1.comp_tendsto hφ, h.2.comp_tendsto hφ⟩

theorem HasOrderLevel.ne_zero_of_lower_bound {s : OrderScales} {f : ℕ → ℂ}
    {k : Fin 6} (h : HasOrderLevel s f k) (hb : s.lower =O[atTop] f) : k ≠ 0 := by
  intro hk
  subst k
  exact isLittleO_irrefl s.lower_nonzero.frequently (hb.trans_isLittleO h)

theorem HasOrderLevel.littleO_upper_of_ne_five {s : OrderScales} {f : ℕ → ℂ}
    {k : Fin 6} (h : HasOrderLevel s f k) (hk : k ≠ 5) : f =o[atTop] s.upper := by
  fin_cases k
  · exact h.trans_isBigO s.lower_upper.isBigO
  · exact h.trans_isLittleO s.lower_upper
  · exact h.2.trans_isBigO s.middle_upper.isBigO
  · exact h.trans_isLittleO s.middle_upper
  · exact h.2
  · exact (hk rfl).elim

theorem HasOrderLevel.five_iff_theta_upper {s : OrderScales} {f : ℕ → ℂ}
    {k : Fin 6} (h : HasOrderLevel s f k) : k = 5 ↔ f =Θ[atTop] s.upper := by
  constructor
  · rintro rfl
    exact h
  · intro ht
    by_contra hk
    exact isLittleO_irrefl s.upper_nonzero.frequently
      (ht.symm.trans_isLittleO (h.littleO_upper_of_ne_five hk))

theorem HasOrderLevel.ne_five_iff_littleO_upper {s : OrderScales} {f : ℕ → ℂ}
    {k : Fin 6} (h : HasOrderLevel s f k) : k ≠ 5 ↔ f =o[atTop] s.upper := by
  refine ⟨h.littleO_upper_of_ne_five, ?_⟩
  intro ho hk
  have ht := h.five_iff_theta_upper.mp hk
  exact isLittleO_irrefl s.upper_nonzero.frequently (ht.symm.trans_isLittleO ho)

theorem exists_orderLevel_of_comparisons (s : OrderScales) (f : ℕ → ℂ)
    (hb : f =O[atTop] s.upper)
    (hl : f =o[atTop] s.lower ∨ f =Θ[atTop] s.lower ∨ s.lower =o[atTop] f)
    (hm : f =o[atTop] s.middle ∨ f =Θ[atTop] s.middle ∨ s.middle =o[atTop] f)
    (hu : f =o[atTop] s.upper ∨ f =Θ[atTop] s.upper ∨ s.upper =o[atTop] f) :
    ∃ k : Fin 6, HasOrderLevel s f k := by
  rcases hu with hu | hu | hu
  · rcases hm with hm | hm | hm
    · rcases hl with hl | hl | hl
      · exact ⟨0, hl⟩
      · exact ⟨1, hl⟩
      · exact ⟨2, hl, hm⟩
    · exact ⟨3, hm⟩
    · exact ⟨4, hm, hu⟩
  · exact ⟨5, hu⟩
  · exact (isLittleO_irrefl s.upper_nonzero.frequently (hu.trans_isBigO hb)).elim

theorem exists_simultaneous_order_levels_for_scales {ι : Type*} [Fintype ι]
    (s : ι → OrderScales) (f : ι → ℕ → ℂ) (hb : ∀ i, f i =O[atTop] (s i).upper) :
    ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ, ∃ k : ι → Fin 6,
      ∀ i, HasOrderLevel ((s i).comp φ hφ.tendsto_atTop) (f i ∘ φ) (k i) := by
  let scale (i : ι) : Fin 3 → ℕ → ℂ := ![(s i).lower, (s i).middle, (s i).upper]
  have hscale : ∀ p : ι × Fin 3, ∀ᶠ t in atTop, scale p.1 p.2 t ≠ 0 := by
    rintro ⟨i, j⟩
    fin_cases j
    · exact (s i).lower_nonzero
    · exact (s i).middle_nonzero
    · exact (s i).upper_nonzero
  obtain ⟨φ, hφ, hc⟩ := exists_simultaneous_order_trichotomy
    (fun p : ι × Fin 3 => f p.1) (fun p => scale p.1 p.2) hscale
  have hk : ∀ i, ∃ k : Fin 6,
      HasOrderLevel ((s i).comp φ hφ.tendsto_atTop) (f i ∘ φ) k := by
    intro i
    exact exists_orderLevel_of_comparisons ((s i).comp φ hφ.tendsto_atTop) (f i ∘ φ)
      ((hb i).comp_tendsto hφ.tendsto_atTop) (hc (i, 0)) (hc (i, 1)) (hc (i, 2))
  choose k hk using hk
  exact ⟨φ, hφ, k, hk⟩

theorem exists_simultaneous_order_levels {ι : Type*} [Fintype ι]
    (s : OrderScales) (f : ι → ℕ → ℂ) (hb : ∀ i, f i =O[atTop] s.upper) :
    ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ, ∃ k : ι → Fin 6,
      ∀ i, HasOrderLevel (s.comp φ hφ.tendsto_atTop) (f i ∘ φ) (k i) :=
  exists_simultaneous_order_levels_for_scales (fun _ => s) f hb

end CentralConfigurations
