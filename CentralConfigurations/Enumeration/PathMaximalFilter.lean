import CentralConfigurations.Diagrams.PathMaximalOrders
import CentralConfigurations.Enumeration.SourceMaximalOrders

/-!
# The complete OrderQ3 path filter from Proposition 4.15

For each increasing triple the Appendix II test checks all three possible
middle vertices and both colors. Each local check rejects a middle row equal
to the endpoint pair, or three rows whose union stays within the triple.
MaxOrderZ/W provide the certified covers internally.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

def pathCandidateCheck {n : ℕ} (A : BinaryMatrixCode n) (M : Fin n → Finset (Fin n))
    (i j k : Fin n) : Bool :=
  if A (upperIndex i j) = true ∧ A (upperIndex j k) = true ∧ A (upperIndex i k) = false then
    decide (M j ≠ {i, k} ∧ ¬ M i ∪ M j ∪ M k ⊆ {i, j, k})
  else true

theorem pathCandidateCheck_of_obstruction {n : ℕ}
    (A : BinaryMatrixCode n) (M : Fin n → Finset (Fin n)) (i j k : Fin n)
    (h : A (upperIndex i j) = true → A (upperIndex j k) = true → A (upperIndex i k) = false →
      M j ≠ {i, k} ∧ ∃ p ∈ ({i, j, k} : Finset (Fin n)), ¬ M p ⊆ {i, j, k}) :
    pathCandidateCheck A M i j k = true := by
  unfold pathCandidateCheck
  split_ifs with he
  · apply decide_eq_true
    obtain ⟨hpair, p, hp, hout⟩ := h he.1 he.2.1 he.2.2
    refine ⟨hpair, fun hs => ?_⟩
    have hu := Finset.union_subset_iff.mp hs
    have hu' := Finset.union_subset_iff.mp hu.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl
    · exact hout hu'.1
    · exact hout hu'.2
    · exact hout hu.2
  · rfl

def pathMaximalTripleCheck {n : ℕ} (d : DiagramCode n)
    (Mz Mw : Fin n → Finset (Fin n)) (i j k : Fin n) : Bool :=
  pathCandidateCheck d.1 Mw i j k &&
    (pathCandidateCheck d.2 Mz i j k &&
    (pathCandidateCheck d.1 Mw j k i &&
    (pathCandidateCheck d.2 Mz j k i &&
    (pathCandidateCheck d.1 Mw k i j && pathCandidateCheck d.2 Mz k i j))))

def sourcePathMaximalCheck {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n)) : Bool :=
  let Mz := sourceMaxOrderZ d B
  let Mw := sourceMaxOrderW d B
  decide (∀ i j k, i < j → j < k → pathMaximalTripleCheck d Mz Mw i j k = true)

/-- The conjunction of the three source OrderQ checks; Rule2hQ is separate. -/
def sourceOrderQ123 {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n)) : Bool :=
  sourceMaximalChecks d B && sourcePathMaximalCheck d B

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem z_pathCandidateCheck (hm : AdmissibleMasses mass)
    (M : Fin n → Finset (Fin n))
    (hM : ∀ p, MaximalTermCover (fun a t => (q t).wEquationTerm p a) (M p))
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    pathCandidateCheck l.diagramCode.1 M i j k = true := by
  classical
  apply pathCandidateCheck_of_obstruction
  intro h₁ h₂ h₃
  exact l.z_path_maximal_covers hb hm M hM i j k hij hjk hik
    (by simpa [l.diagramCode_z_entry, OneColorLimit.Incident, hij] using h₁)
    (by simpa [l.diagramCode_z_entry, OneColorLimit.Incident, hjk] using h₂)
    (by simpa [l.diagramCode_z_entry, OneColorLimit.Incident, hik] using h₃)

theorem w_pathCandidateCheck (hm : AdmissibleMasses mass)
    (M : Fin n → Finset (Fin n))
    (hM : ∀ p, MaximalTermCover (fun a t => (q t).zEquationTerm p a) (M p))
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    pathCandidateCheck l.diagramCode.2 M i j k = true := by
  classical
  apply pathCandidateCheck_of_obstruction
  intro h₁ h₂ h₃
  exact l.w_path_maximal_covers hb hm M hM i j k hij hjk hik
    (by simpa [l.diagramCode_w_entry, OneColorLimit.Incident, hij] using h₁)
    (by simpa [l.diagramCode_w_entry, OneColorLimit.Incident, hjk] using h₂)
    (by simpa [l.diagramCode_w_entry, OneColorLimit.Incident, hik] using h₃)

end ScaledZWLimit

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
variable (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode)
include o hb hB

theorem source_path_maximal_check (hm : AdmissibleMasses mass) :
    sourcePathMaximalCheck l.diagramCode B = true := by
  have hm' (j) : mass j ≠ 0 := by simpa using hm {j} (Finset.singleton_nonempty j)
  have hMz := o.sourceMaxOrderZ_cover l hb B hB hm'
  have hMw := o.sourceMaxOrderW_cover l hb B hB hm'
  apply decide_eq_true
  intro i j k hij hjk
  have hik := (lt_trans hij hjk).ne
  simp only [pathMaximalTripleCheck, Bool.and_eq_true]
  exact ⟨l.z_pathCandidateCheck hb hm _ hMw i j k hij.ne hjk.ne hik,
    l.w_pathCandidateCheck hb hm _ hMz i j k hij.ne hjk.ne hik,
    l.z_pathCandidateCheck hb hm _ hMw j k i hjk.ne (Ne.symm hik) (Ne.symm hij.ne),
    l.w_pathCandidateCheck hb hm _ hMz j k i hjk.ne (Ne.symm hik) (Ne.symm hij.ne),
    l.z_pathCandidateCheck hb hm _ hMw k i j (Ne.symm hik) hij.ne (Ne.symm hjk.ne),
    l.w_pathCandidateCheck hb hm _ hMz k i j (Ne.symm hik) hij.ne (Ne.symm hjk.ne)⟩

theorem source_orderQ123 (hm : AdmissibleMasses mass) : sourceOrderQ123 l.diagramCode B = true := by
  unfold sourceOrderQ123
  rw [Bool.and_eq_true]
  exact ⟨o.source_maximalChecks l hb B hB hm, o.source_path_maximal_check l hb B hB hm⟩

end SequenceOrderAssignment

theorem ZWOrderCoverage.filter_sourcePathMaximalCheck {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha
      (C.filter (fun B => sourcePathMaximalCheck l.diagramCode B = true)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨B, Finset.mem_filter.mpr ⟨hB,
    o.source_path_maximal_check (l.comp φ hφ.tendsto_atTop) (fun t => hb (φ t)) B ho hm⟩, ho⟩

theorem ZWOrderCoverage.filter_sourceOrderQ123 {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (C.filter (fun B => sourceOrderQ123 l.diagramCode B = true)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨B, Finset.mem_filter.mpr ⟨hB,
    o.source_orderQ123 (l.comp φ hφ.tendsto_atTop) (fun t => hb (φ t)) B ho hm⟩, ho⟩

end CentralConfigurations
