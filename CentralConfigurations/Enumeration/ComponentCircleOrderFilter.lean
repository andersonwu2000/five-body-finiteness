import CentralConfigurations.Diagrams.ComponentCirclePairs
import CentralConfigurations.Enumeration.SequenceOrderDomains
import Mathlib.Data.Finset.Prod

/-!
# Proposition 4.12 and the actual Appendix II Rule1cQ

Nonempty circled subsets have two distinct leading positions. Their
separation therefore has level 5. The numerical filter counts both
orientations and diagonal entries, as the appendix does. Empty circled
subsets are skipped, exactly as in the printed program.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

def componentCircles {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ) (s : Finset (Fin n)) :
    Finset (Fin n) := s.filter (fun i => A i i = 1)

def componentLevelFiveCount {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (J : Finset (Fin n)) : ℕ :=
  ((J ×ˢ J).filter (fun p => (5 : Fin 6) ∈ B (zwOrderSlot color p.1 p.2))).card

def componentCircleMassCheck {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (B : OrderBox (ZWOrderIndex n)) (color : Fin 2) (s : Finset (Fin n)) : Bool :=
  let J := componentCircles A s
  decide (J = ∅ ∨ componentLevelFiveCount B color J ≠ J.card)

def appendixCircleMassCheck {n : ℕ} (A W : Matrix (Fin n) (Fin n) ℕ)
    (B : OrderBox (ZWOrderIndex n)) : Bool :=
  (appendixComponents A).all (componentCircleMassCheck A B 0) &&
    (appendixComponents W).all (componentCircleMassCheck W B 1)

theorem componentLevelFiveCount_gt_card {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (J : Finset (Fin n))
    (hdiag : ∀ i ∈ J, (5 : Fin 6) ∈ B (zwOrderSlot color i i))
    (i j : Fin n) (hi : i ∈ J) (hj : j ∈ J) (hij : i ≠ j)
    (hp : (5 : Fin 6) ∈ B (zwOrderSlot color i j)) :
    J.card < componentLevelFiveCount B color J := by
  have hsub : J.diag ⊆ (J ×ˢ J).filter (fun p => (5 : Fin 6) ∈ B (zwOrderSlot color p.1 p.2)) := by
    intro p hp
    obtain ⟨hip, heq⟩ := Finset.mem_diag.mp hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨hip, heq ▸ hip⟩, ?_⟩
    simpa only [← heq] using hdiag p.1 hip
  have hproper : J.diag ⊂ (J ×ˢ J).filter
      (fun p => (5 : Fin 6) ∈ B (zwOrderSlot color p.1 p.2)) := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub, ?_⟩
    intro heq
    have hm : (i, j) ∈ J.diag := by
      rw [heq]
      exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hi, hj⟩, hp⟩
    exact hij (Finset.mem_diag.mp hm).2
  simpa only [Finset.diag_card] using Finset.card_lt_card hproper

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))

theorem z_circle_pair_level_five (hm : AdmissibleMasses mass)
    (s c : Finset (Fin n)) (his : MatrixIsolated l.z.matrix c)
    (hcover : MatrixCircleCover l.z.matrix s c) (hJ : (componentCircles l.z.matrix s).Nonempty) :
    ∃ i ∈ componentCircles l.z.matrix s, ∃ j ∈ componentCircles l.z.matrix s,
      i ≠ j ∧ o.z i j = 5 := by
  obtain ⟨i, hi⟩ := hJ
  have hci := Finset.mem_filter.mp hi
  obtain ⟨j, hjs, hjc, hpos⟩ := l.z.distinct_circle_of_cover hm s c his hcover i hci.1 hci.2
  have hij : i ≠ j := fun h => hpos (congrArg l.z.position h)
  exact ⟨i, hi, j, Finset.mem_filter.mpr ⟨hjs, hjc⟩, hij,
    (o.z_offDiagonal_five_iff l i j hij).mpr hpos⟩

theorem w_circle_pair_level_five (hm : AdmissibleMasses mass)
    (s c : Finset (Fin n)) (his : MatrixIsolated l.w.matrix c)
    (hcover : MatrixCircleCover l.w.matrix s c) (hJ : (componentCircles l.w.matrix s).Nonempty) :
    ∃ i ∈ componentCircles l.w.matrix s, ∃ j ∈ componentCircles l.w.matrix s,
      i ≠ j ∧ o.w i j = 5 := by
  obtain ⟨i, hi⟩ := hJ
  have hci := Finset.mem_filter.mp hi
  obtain ⟨j, hjs, hjc, hpos⟩ := l.w.distinct_circle_of_cover hm s c his hcover i hci.1 hci.2
  have hij : i ≠ j := fun h => hpos (congrArg l.w.position h)
  exact ⟨i, hi, j, Finset.mem_filter.mpr ⟨hjs, hjc⟩, hij,
    (o.w_offDiagonal_five_iff l i j hij).mpr hpos⟩

theorem z_source_circle_pair_level_five (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : SourceConnectedComponent l.z.matrix s)
    (hJ : (componentCircles l.z.matrix s).Nonempty) :
    ∃ i ∈ componentCircles l.z.matrix s, ∃ j ∈ componentCircles l.z.matrix s,
      i ≠ j ∧ o.z i j = 5 := by
  obtain ⟨r, hr⟩ := hs.nonempty
  exact o.z_circle_pair_level_five l hm s _
    (ordinaryComponent_isolated _ _ r) (hs.circle_cover r hr) hJ

theorem w_source_circle_pair_level_five (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : SourceConnectedComponent l.w.matrix s)
    (hJ : (componentCircles l.w.matrix s).Nonempty) :
    ∃ i ∈ componentCircles l.w.matrix s, ∃ j ∈ componentCircles l.w.matrix s,
      i ≠ j ∧ o.w i j = 5 := by
  obtain ⟨r, hr⟩ := hs.nonempty
  exact o.w_circle_pair_level_five l hm s _
    (ordinaryComponent_isolated _ _ r) (hs.circle_cover r hr) hJ

theorem z_circle_mass_check_of_cover (hm : AdmissibleMasses mass)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode)
    (s c : Finset (Fin n)) (his : MatrixIsolated l.z.matrix c)
    (hcover : MatrixCircleCover l.z.matrix s c) :
    componentCircleMassCheck l.z.matrix B 0 s = true := by
  apply decide_eq_true (p := componentCircles l.z.matrix s = ∅ ∨
    componentLevelFiveCount B 0 (componentCircles l.z.matrix s) ≠ (componentCircles l.z.matrix s).card)
  by_cases hJ : (componentCircles l.z.matrix s).Nonempty
  · right
    obtain ⟨i, hi, j, hj, hij, hl⟩ := o.z_circle_pair_level_five l hm s c his hcover hJ
    apply ne_of_gt (componentLevelFiveCount_gt_card B 0 _ ?_ i j hi hj hij ?_)
    · intro k hk
      have hkc := (Finset.mem_filter.mp hk).2
      have hlk : o.z k k = 5 := (o.z_diagonal_five_iff l k).mpr (by
        simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hkc)
      simpa only [orderCode_z, hlk] using hB (zwOrderSlot 0 k k)
    · simpa only [orderCode_z, hl] using hB (zwOrderSlot 0 i j)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hJ)

theorem w_circle_mass_check_of_cover (hm : AdmissibleMasses mass)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode)
    (s c : Finset (Fin n)) (his : MatrixIsolated l.w.matrix c)
    (hcover : MatrixCircleCover l.w.matrix s c) :
    componentCircleMassCheck l.w.matrix B 1 s = true := by
  apply decide_eq_true (p := componentCircles l.w.matrix s = ∅ ∨
    componentLevelFiveCount B 1 (componentCircles l.w.matrix s) ≠ (componentCircles l.w.matrix s).card)
  by_cases hJ : (componentCircles l.w.matrix s).Nonempty
  · right
    obtain ⟨i, hi, j, hj, hij, hl⟩ := o.w_circle_pair_level_five l hm s c his hcover hJ
    apply ne_of_gt (componentLevelFiveCount_gt_card B 1 _ ?_ i j hi hj hij ?_)
    · intro k hk
      have hkc := (Finset.mem_filter.mp hk).2
      have hlk : o.w k k = 5 := (o.w_diagonal_five_iff l k).mpr (by
        simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hkc)
      simpa only [orderCode_w, hlk] using hB (zwOrderSlot 1 k k)
    · simpa only [orderCode_w, hl] using hB (zwOrderSlot 1 i j)
  · exact Or.inl (Finset.not_nonempty_iff_eq_empty.mp hJ)

theorem z_appendix_circle_mass_check (hm : AdmissibleMasses mass)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode)
    (s : Finset (Fin n)) (hs : s ∈ appendixComponents l.z.matrix) :
    componentCircleMassCheck l.z.matrix B 0 s = true := by
  by_cases hc : ∃ i ∈ s, l.z.matrix i i = 1
  · obtain ⟨r, hcover⟩ := l.z.appendix_component_circle_cover s hs hc
    exact o.z_circle_mass_check_of_cover l hm B hB s _
      (ordinaryComponent_isolated _ _ r) hcover
  · have he : componentCircles l.z.matrix s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hc ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
    simp [componentCircleMassCheck, he]

theorem w_appendix_circle_mass_check (hm : AdmissibleMasses mass)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode)
    (s : Finset (Fin n)) (hs : s ∈ appendixComponents l.w.matrix) :
    componentCircleMassCheck l.w.matrix B 1 s = true := by
  by_cases hc : ∃ i ∈ s, l.w.matrix i i = 1
  · obtain ⟨r, hcover⟩ := l.w.appendix_component_circle_cover s hs hc
    exact o.w_circle_mass_check_of_cover l hm B hB s _
      (ordinaryComponent_isolated _ _ r) hcover
  · have he : componentCircles l.w.matrix s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      exact hc ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
    simp [componentCircleMassCheck, he]

theorem appendix_circle_mass_check (hm : AdmissibleMasses mass)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    appendixCircleMassCheck l.z.matrix l.w.matrix B = true := by
  unfold appendixCircleMassCheck
  rw [Bool.and_eq_true]
  exact ⟨List.all_eq_true.mpr (fun s hs => o.z_appendix_circle_mass_check l hm B hB s hs),
    List.all_eq_true.mpr (fun s hs => o.w_appendix_circle_mass_check l hm B hB s hs)⟩

end SequenceOrderAssignment

theorem ZWOrderCoverage.filter_appendixCircleMassCheck {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha
      (C.filter (fun B => appendixCircleMassCheck l.z.matrix l.w.matrix B = true)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨B, Finset.mem_filter.mpr ⟨hB,
    o.appendix_circle_mass_check (l.comp φ hφ.tendsto_atTop) hm B ho⟩, ho⟩

end CentralConfigurations
