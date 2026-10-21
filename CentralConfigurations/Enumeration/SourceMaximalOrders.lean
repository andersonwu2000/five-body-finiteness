import CentralConfigurations.Enumeration.SourceRowComparisons
import CentralConfigurations.Enumeration.MaximalTermFilters

/-!
# MaxOrderZ/W and the certified 4.13--4.14 filters

Each row visits all unordered off-diagonal pairs in increasing index order,
then compares its diagonal with the current off-diagonal entry, just as the
Appendix II loops do. Deleting a term does not require its witness to remain.
All comparison certificates are constructed from the finite input domains.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

def compareMaxOrderRow {n : ℕ} (A A' : BinaryMatrixCode n)
    (B B' : Fin n → Fin n → Finset (Fin 6)) (D : OrderBox (ROrderIndex n))
    (i j k : Fin n) : OrderComparison :=
  if j = i then
    if k = i then .unknown else comparePositionForceRow A B D i k
  else if k = i then (comparePositionForceRow A B D i j).flip
  else compareForceRow A A' B B' D i j k

def maxOrderComparisonPairs {n : ℕ} (i : Fin n) : List (Fin n × Fin n) :=
  (List.finRange n).flatMap fun j =>
    if j = i then [] else
      (((List.finRange n).filter fun k => decide (k ≠ i ∧ j < k)).map fun k => (j, k)) ++ [(i, j)]

def comparisonDelete {ι : Type*} [DecidableEq ι] (c : ι → ι → OrderComparison)
    (M : Finset ι) (p : ι × ι) : Finset ι :=
  match c p.1 p.2 with
  | .less => M.erase p.1
  | .greater => M.erase p.2
  | _ => M

def comparisonSweep {ι : Type*} [DecidableEq ι] (c : ι → ι → OrderComparison)
    (pairs : List (ι × ι)) (M : Finset ι) : Finset ι := pairs.foldl (comparisonDelete c) M

theorem MaximalTermCover.comparisonDelete {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℕ → ℂ} {M : Finset ι} (h : MaximalTermCover f M)
    {c : ι → ι → OrderComparison} (hc : ∀ i j, (c i j).Valid (f i) (f j)) (p : ι × ι) :
    MaximalTermCover f (comparisonDelete c M p) := by
  have hp := hc p.1 p.2
  unfold CentralConfigurations.comparisonDelete
  cases he : c p.1 p.2 with
  | unknown => exact h
  | less => exact h.erase_of_littleO (by simpa only [he, OrderComparison.Valid] using hp)
  | equal => exact h
  | greater => exact h.erase_of_littleO (by simpa only [he, OrderComparison.Valid] using hp)

theorem MaximalTermCover.comparisonSweep {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℕ → ℂ} {M : Finset ι} (h : MaximalTermCover f M)
    {c : ι → ι → OrderComparison} (hc : ∀ i j, (c i j).Valid (f i) (f j))
    (pairs : List (ι × ι)) : MaximalTermCover f (comparisonSweep c pairs M) := by
  induction pairs generalizing M with
  | nil => exact h
  | cons p pairs ih => exact ih (h.comparisonDelete hc p)

def maxOrderWithDistances {n : ℕ} (A A' : BinaryMatrixCode n)
    (B B' : Fin n → Fin n → Finset (Fin 6)) (D : OrderBox (ROrderIndex n))
    (i : Fin n) : Finset (Fin n) :=
  comparisonSweep (compareMaxOrderRow A A' B B' D i) (maxOrderComparisonPairs i) Finset.univ

def sourceMaxOrderZ {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n))
    (i : Fin n) : Finset (Fin n) :=
  maxOrderWithDistances d.1 d.2 (fun a b => B (zwOrderSlot 0 a b))
    (fun a b => B (zwOrderSlot 1 a b)) (producedDistanceBox d B) i

def sourceMaxOrderW {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n))
    (i : Fin n) : Finset (Fin n) :=
  maxOrderWithDistances d.2 d.1 (fun a b => B (zwOrderSlot 1 a b))
    (fun a b => B (zwOrderSlot 0 a b)) (producedDistanceBox d B) i

def sourceMaximalChecks {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n)) : Bool :=
  maximalRowCountCheck (sourceMaxOrderZ d B) (sourceMaxOrderW d B) &&
    maximalPairDistanceCheck (sourceMaxOrderZ d B) (sourceMaxOrderW d B) (producedDistanceBox d B)

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
variable (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode)
variable (D : OrderBox (ROrderIndex n)) (hD : D.Admits o.radiusCode)
include o hb hB hD

theorem compare_z_maxRow_valid (i j k : Fin n) :
    (compareMaxOrderRow l.diagramCode.1 l.diagramCode.2
      (fun a b => B (zwOrderSlot 0 a b)) (fun a b => B (zwOrderSlot 1 a b)) D i j k).Valid
      (fun t => (q t).zMaxTermValue i j) (fun t => (q t).zMaxTermValue i k) := by
  unfold compareMaxOrderRow
  split_ifs with hji hki hki
  · trivial
  · subst j
    simpa only [ZWSystem.zMaxTermValue, if_pos rfl, if_neg (Ne.symm hki)] using
      o.compare_position_zForce_row_valid l hb B hB D hD i k (Ne.symm hki)
  · subst k
    simpa only [ZWSystem.zMaxTermValue, if_pos rfl, if_neg (Ne.symm hji)] using
      (o.compare_position_zForce_row_valid l hb B hB D hD i j (Ne.symm hji)).flip
  · simpa only [ZWSystem.zMaxTermValue, if_neg (Ne.symm hji), if_neg (Ne.symm hki)] using
      o.compare_zForce_row_valid l hb B hB D hD i j k (Ne.symm hji) (Ne.symm hki)

theorem compare_w_maxRow_valid (i j k : Fin n) :
    (compareMaxOrderRow l.diagramCode.2 l.diagramCode.1
      (fun a b => B (zwOrderSlot 1 a b)) (fun a b => B (zwOrderSlot 0 a b)) D i j k).Valid
      (fun t => (q t).wMaxTermValue i j) (fun t => (q t).wMaxTermValue i k) := by
  unfold compareMaxOrderRow
  split_ifs with hji hki hki
  · trivial
  · subst j
    simpa only [ZWSystem.wMaxTermValue, if_pos rfl, if_neg (Ne.symm hki)] using
      o.compare_position_wForce_row_valid l hb B hB D hD i k (Ne.symm hki)
  · subst k
    simpa only [ZWSystem.wMaxTermValue, if_pos rfl, if_neg (Ne.symm hji)] using
      (o.compare_position_wForce_row_valid l hb B hB D hD i j (Ne.symm hji)).flip
  · simpa only [ZWSystem.wMaxTermValue, if_neg (Ne.symm hji), if_neg (Ne.symm hki)] using
      o.compare_wForce_row_valid l hb B hB D hD i j k (Ne.symm hji) (Ne.symm hki)

theorem z_maxOrderWithDistances_cover (hm : ∀ j, mass j ≠ 0) (i : Fin n) :
    MaximalTermCover (fun j t => (q t).zEquationTerm i j)
      (maxOrderWithDistances l.diagramCode.1 l.diagramCode.2
        (fun a b => B (zwOrderSlot 0 a b)) (fun a b => B (zwOrderSlot 1 a b)) D i) := by
  apply (maximalTermCover_univ _).comparisonSweep
  intro j k
  exact (o.compare_z_maxRow_valid l hb B hB D hD i j k).congr_theta
    (ZWSystem.zMaxTermValue_theta_equationTerm q hm i j)
    (ZWSystem.zMaxTermValue_theta_equationTerm q hm i k)

theorem w_maxOrderWithDistances_cover (hm : ∀ j, mass j ≠ 0) (i : Fin n) :
    MaximalTermCover (fun j t => (q t).wEquationTerm i j)
      (maxOrderWithDistances l.diagramCode.2 l.diagramCode.1
        (fun a b => B (zwOrderSlot 1 a b)) (fun a b => B (zwOrderSlot 0 a b)) D i) := by
  apply (maximalTermCover_univ _).comparisonSweep
  intro j k
  exact (o.compare_w_maxRow_valid l hb B hB D hD i j k).congr_theta
    (ZWSystem.wMaxTermValue_theta_equationTerm q hm i j)
    (ZWSystem.wMaxTermValue_theta_equationTerm q hm i k)

omit hD

theorem sourceMaxOrderZ_cover (hm : ∀ j, mass j ≠ 0) (i : Fin n) :
    MaximalTermCover (fun j t => (q t).zEquationTerm i j) (sourceMaxOrderZ l.diagramCode B i) :=
  o.z_maxOrderWithDistances_cover l hb B hB _ (o.admitted_producedDistanceBox l hb B hB) hm i

theorem sourceMaxOrderW_cover (hm : ∀ j, mass j ≠ 0) (i : Fin n) :
    MaximalTermCover (fun j t => (q t).wEquationTerm i j) (sourceMaxOrderW l.diagramCode B i) :=
  o.w_maxOrderWithDistances_cover l hb B hB _ (o.admitted_producedDistanceBox l hb B hB) hm i

/-- Proposition 4.13 for the concrete finite source comparator. -/
theorem source_maximalRowCountCheck (hm : AdmissibleMasses mass) :
    maximalRowCountCheck (sourceMaxOrderZ l.diagramCode B) (sourceMaxOrderW l.diagramCode B) = true := by
  have hm' (j) : mass j ≠ 0 := by simpa using hm {j} (Finset.singleton_nonempty j)
  exact maximalRowCountCheck_of_covers q hm i₀ j₀ hij₀ _ _
    (o.sourceMaxOrderZ_cover l hb B hB hm') (o.sourceMaxOrderW_cover l hb B hB hm')

/-- Proposition 4.14 for the same concrete comparator and produced distance box. -/
theorem source_maximalPairDistanceCheck (hm : AdmissibleMasses mass) :
    maximalPairDistanceCheck (sourceMaxOrderZ l.diagramCode B) (sourceMaxOrderW l.diagramCode B)
      (producedDistanceBox l.diagramCode B) = true := by
  have hm' (j) : mass j ≠ 0 := by simpa using hm {j} (Finset.singleton_nonempty j)
  exact o.maximalPairDistanceCheck_of_covers hm _ _ _ (o.admitted_producedDistanceBox l hb B hB)
    (o.sourceMaxOrderZ_cover l hb B hB hm') (o.sourceMaxOrderW_cover l hb B hB hm')

theorem source_maximalChecks (hm : AdmissibleMasses mass) :
    sourceMaximalChecks l.diagramCode B = true := by
  unfold sourceMaximalChecks
  rw [Bool.and_eq_true]
  exact ⟨o.source_maximalRowCountCheck l hb B hB hm, o.source_maximalPairDistanceCheck l hb B hB hm⟩

end SequenceOrderAssignment

theorem ZWOrderCoverage.filter_sourceMaximalChecks {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (C.filter (fun B => sourceMaximalChecks l.diagramCode B = true)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨B, Finset.mem_filter.mpr ⟨hB,
    o.source_maximalChecks (l.comp φ hφ.tendsto_atTop) (fun t => hb (φ t)) B ho hm⟩, ho⟩

end CentralConfigurations
