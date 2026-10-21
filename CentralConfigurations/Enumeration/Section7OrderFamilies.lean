import CentralConfigurations.Enumeration.SourceUpdateTermination
import CentralConfigurations.Enumeration.OrderBranchingProcess
import CentralConfigurations.Enumeration.PathMaximalFilter
import CentralConfigurations.Enumeration.ComponentCircleOrderFilter
import CentralConfigurations.Enumeration.DistanceOrderDomains

/-!
# Section 7: finite Type 2 and Type 3 covering families

This module assembles contracting updates and criteria (4.12)--(4.15).
SourceUpdateTermination.lean provides the product-count stopping argument.
The update schedule is a finite list. The coverage results concern the Lean
operations; they do not assert equivalence with a Mathematica execution or
require quotienting the output by permutations.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

def offDiagonalOrderSlots (n : ℕ) : List (ZWOrderIndex n) :=
  (List.finRange 2).flatMap fun c => (List.finRange n).flatMap fun i =>
    ((List.finRange n).filter (fun j => i < j)).map (fun j => zwOrderSlot c i j)

def diagonalOrderSlots (n : ℕ) : List (ZWOrderIndex n) :=
  (List.finRange 2).flatMap fun c => (List.finRange n).map (fun i => zwOrderSlot c i i)

theorem mem_offDiagonalOrderSlots {n : ℕ} (p : ZWOrderIndex n)
    (hp : p.2.1.1 ≠ p.2.1.2) : p ∈ offDiagonalOrderSlots n := by
  rcases p with ⟨c,⟨⟨i,j⟩,hij⟩⟩
  apply List.mem_flatMap.mpr
  refine ⟨c,by simp,List.mem_flatMap.mpr ⟨i,by simp,?_⟩⟩
  apply List.mem_map.mpr
  refine ⟨j,by simp [lt_of_le_of_ne hij hp],?_⟩
  simp [zwOrderSlot,upperIndex,min_eq_left hij,max_eq_right hij]

theorem mem_diagonalOrderSlots {n : ℕ} (p : ZWOrderIndex n)
    (hp : p.2.1.1 = p.2.1.2) : p ∈ diagonalOrderSlots n := by
  rcases p with ⟨c,⟨⟨i,j⟩,hij⟩⟩
  dsimp at hp
  subst j
  apply List.mem_flatMap.mpr
  refine ⟨c,by simp,List.mem_map.mpr ⟨i,by simp,?_⟩⟩
  simp [zwOrderSlot,upperIndex]

def IsType2OrderBox {n : ℕ} (B : OrderBox (ZWOrderIndex n)) : Prop :=
  (∀ p, (B p).Nonempty) ∧ ∀ p, p.2.1.1 ≠ p.2.1.2 → (B p).card = 1

def IsType3OrderBox {n : ℕ} (B : OrderBox (ZWOrderIndex n)) : Prop :=
  ∀ p, (B p).card = 1

theorem isType3OrderBox_iff_count_one {n : ℕ} (B : OrderBox (ZWOrderIndex n)) :
    IsType3OrderBox B ↔ OrderBox.completionCount B = 1 :=
  (OrderBox.completionCount_one_iff B).symm

theorem IsType3OrderBox.isType2 {n : ℕ} {B : OrderBox (ZWOrderIndex n)}
    (hB : IsType3OrderBox B) : IsType2OrderBox B :=
  ⟨fun p => Finset.card_pos.mp (by rw [hB p]; decide),fun p _ => hB p⟩

def splitSourceOrderFamily {n : ℕ} (d : DiagramCode n) (ops : List (SourceUpdateOp n))
    (slots : List (ZWOrderIndex n)) (C : Finset (OrderBox (ZWOrderIndex n))) :=
  OrderBox.splitRefine (stabilizedSourceUpdate d ops) slots C

theorem mem_splitSourceOrderFamily_fixed {n : ℕ} (d : DiagramCode n)
    (ops : List (SourceUpdateOp n)) (slots : List (ZWOrderIndex n))
    (C : Finset (OrderBox (ZWOrderIndex n))) (D : OrderBox (ZWOrderIndex n))
    (hD : D ∈ splitSourceOrderFamily d ops slots C) : sourceUpdateSweep d ops D = D := by
  have hN := (OrderBox.mem_splitRefine_properties _ (stabilizedSourceUpdate_refines d ops)
    slots C D hD).1
  obtain ⟨B,hB⟩ := OrderBox.mem_splitRefine_last _ slots C D hD
  rcases stabilizedSourceUpdate_terminal d ops B with hz | hf
  · rw [hB] at hz
    exact (Nat.ne_of_gt ((OrderBox.completionCount_pos_iff D).mpr hN) hz).elim
  · simpa only [hB] using hf

/-- The four feasibility criteria whose admission theorems are established. -/
def section7ProvedCriteria {n : ℕ} (d : DiagramCode n)
    (B : OrderBox (ZWOrderIndex n)) : Bool :=
  sourceOrderQ123 d B && appendixCircleMassCheck
    (BinaryMatrixCode.decode d.1) (BinaryMatrixCode.decode d.2) B

def section7Type2Family {n : ℕ} (d : DiagramCode n) (ops : List (SourceUpdateOp n))
    (C : Finset (OrderBox (ZWOrderIndex n))) : Finset (OrderBox (ZWOrderIndex n)) :=
  (splitSourceOrderFamily d ops (offDiagonalOrderSlots n) C).filter
    (fun B => section7ProvedCriteria d B = true)

def section7Type3Family {n : ℕ} (d : DiagramCode n) (ops : List (SourceUpdateOp n))
    (C₂ : Finset (OrderBox (ZWOrderIndex n))) : Finset (OrderBox (ZWOrderIndex n)) :=
  (splitSourceOrderFamily d ops (diagonalOrderSlots n) C₂).filter
    (fun B => section7ProvedCriteria d B = true)

theorem mem_section7Type2Family {n : ℕ} (d : DiagramCode n) (ops : List (SourceUpdateOp n))
    (C : Finset (OrderBox (ZWOrderIndex n))) (B : OrderBox (ZWOrderIndex n))
    (hB : B ∈ section7Type2Family d ops C) :
    IsType2OrderBox B ∧ (∃ A ∈ C, B.Refines A) ∧
      sourceUpdateSweep d ops B = B ∧ section7ProvedCriteria d B = true := by
  obtain ⟨hB,hcrit⟩ := Finset.mem_filter.mp hB
  obtain ⟨hN,hancestor,hslots⟩ := OrderBox.mem_splitRefine_properties _
    (stabilizedSourceUpdate_refines d ops) _ C B hB
  exact ⟨⟨hN,fun p hp => hslots p (mem_offDiagonalOrderSlots p hp)⟩,
    hancestor,mem_splitSourceOrderFamily_fixed d ops _ C B hB,hcrit⟩

theorem mem_section7Type3Family {n : ℕ} (d : DiagramCode n) (ops : List (SourceUpdateOp n))
    (C₂ : Finset (OrderBox (ZWOrderIndex n)))
    (hC₂ : ∀ A ∈ C₂, IsType2OrderBox A) (B : OrderBox (ZWOrderIndex n))
    (hB : B ∈ section7Type3Family d ops C₂) :
    IsType3OrderBox B ∧ (∃ A ∈ C₂, B.Refines A) ∧
      sourceUpdateSweep d ops B = B ∧ section7ProvedCriteria d B = true := by
  obtain ⟨hB,hcrit⟩ := Finset.mem_filter.mp hB
  obtain ⟨hN,⟨A,hA,hBA⟩,hslots⟩ := OrderBox.mem_splitRefine_properties _
    (stabilizedSourceUpdate_refines d ops) _ C₂ B hB
  refine ⟨?_,⟨A,hA,hBA⟩,mem_splitSourceOrderFamily_fixed d ops _ C₂ B hB,hcrit⟩
  intro p
  by_cases hp : p.2.1.1 = p.2.1.2
  · exact hslots p (mem_diagonalOrderSlots p hp)
  · exact OrderBox.singleton_card_of_refines hBA p (hN p) ((hC₂ A hA).2 p hp)

namespace SequenceOrderAssignment
variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass)
include hb hm

theorem section7_proved_criteria (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) : section7ProvedCriteria l.diagramCode B = true := by
  unfold section7ProvedCriteria
  rw [Bool.and_eq_true]
  refine ⟨o.source_orderQ123 l hb B hB hm,?_⟩
  simpa only [ScaledZWLimit.diagramCode,
    BinaryMatrixCode.decode_encode _ l.z.matrix_binary l.z.matrix_symm,
    BinaryMatrixCode.decode_encode _ l.w.matrix_binary l.w.matrix_symm] using
    o.appendix_circle_mass_check l hm B hB

end SequenceOrderAssignment

namespace ZWOrderCoverage
variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass)
include hC hb hm

theorem splitSourceOrderFamily (ops : List (SourceUpdateOp n))
    (slots : List (ZWOrderIndex n)) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (CentralConfigurations.splitSourceOrderFamily l.diagramCode ops slots C) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  exact OrderBox.covered_splitRefine _ slots C o.orderCode
    (fun B hB => o.admitted_stabilizedSourceUpdate (l.comp φ hφ.tendsto_atTop)
      (fun t => hb (φ t)) hm ops B hB) (hC φ hφ o.orderCode o.hasZWOrderCode)

theorem filter_section7ProvedCriteria :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (C.filter (fun B => section7ProvedCriteria l.diagramCode B = true)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B,hB,ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨B,Finset.mem_filter.mpr ⟨hB,o.section7_proved_criteria
    (l.comp φ hφ.tendsto_atTop) (fun t => hb (φ t)) hm B ho⟩,ho⟩

theorem section7Type2Family (ops : List (SourceUpdateOp n)) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (CentralConfigurations.section7Type2Family l.diagramCode ops C) :=
  (hC.splitSourceOrderFamily l hb hm ops (offDiagonalOrderSlots n)).filter_section7ProvedCriteria l hb hm

theorem section7Type3Family (ops : List (SourceUpdateOp n)) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (CentralConfigurations.section7Type3Family l.diagramCode ops C) :=
  (hC.splitSourceOrderFamily l hb hm ops (diagonalOrderSlots n)).filter_section7ProvedCriteria l hb hm

end ZWOrderCoverage
end CentralConfigurations
