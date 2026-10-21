import CentralConfigurations.Enumeration.SourceOrderRefinement
import CentralConfigurations.Enumeration.ComponentCircleOrderFilter
import CentralConfigurations.Enumeration.MinimumDistanceOrders

/-!
# Kernel-checked exhaustive order refutations

A refutation consists of a proved obstruction, a checked update trace, or
a branch with a proof for each value in the selected domain. Branches may
fix diagonal or separation entries; singleton updates retain symmetry.
Every leaf must be closed to construct a refutation.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

inductive OrderObstruction (n : ℕ) where
  | empty (slot : ZWOrderIndex n)
  | row (color : Fin 2) (i : Fin n)
  | pair (color : Fin 2) (i j : Fin n)
  | path (color : Fin 2) (i j k : Fin n)
  | circle
  | shrinking

def OrderObstruction.check {n : ℕ} (reason : OrderObstruction n)
    (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n)) : Bool :=
  match reason with
  | .empty slot => decide (B slot = ∅)
  | .row c i => decide (((if c = 0 then sourceMaxOrderZ d B else sourceMaxOrderW d B) i).card = 1)
  | .pair c i j => pairOrderObstruction d B c i j
  | .path c i j k =>
      decide (i ≠ j ∧ j ≠ k ∧ i ≠ k) &&
        !(if c = 0 then pathCandidateCheck d.1 (sourceMaxOrderW d B) i j k
          else pathCandidateCheck d.2 (sourceMaxOrderZ d B) i j k)
  | .circle => !(appendixCircleMassCheck (BinaryMatrixCode.decode d.1) (BinaryMatrixCode.decode d.2) B)
  | .shrinking => !(shrinkingRadiusCheck d B)

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass)
include hb hm

theorem orderObstruction_check_false (reason : OrderObstruction n)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    reason.check l.diagramCode B = false := by
  have hm' (j) : mass j ≠ 0 := by simpa using hm {j} (Finset.singleton_nonempty j)
  cases reason with
  | empty slot =>
      apply decide_eq_false
      intro he
      have hmem := hB slot
      simpa [he] using hmem
  | row c i =>
      have h := of_decide_eq_true (o.source_maximalRowCountCheck l hb B hB hm)
      change decide (((if c = 0 then sourceMaxOrderZ l.diagramCode B else sourceMaxOrderW l.diagramCode B) i).card = 1) = false
      apply decide_eq_false
      split_ifs with hc
      · exact (h i).1
      · exact (h i).2
  | pair c i j => exact o.pairOrderObstruction_eq_false l hb hm B hB c i j
  | path c i j k =>
      simp only [OrderObstruction.check]
      by_cases he : i ≠ j ∧ j ≠ k ∧ i ≠ k
      · rw [show decide (i ≠ j ∧ j ≠ k ∧ i ≠ k) = true from decide_eq_true he]
        by_cases hc : c = 0
        · rw [if_pos hc, l.z_pathCandidateCheck hb hm _ (o.sourceMaxOrderW_cover l hb B hB hm') i j k he.1 he.2.1 he.2.2]
          rfl
        · rw [if_neg hc, l.w_pathCandidateCheck hb hm _ (o.sourceMaxOrderZ_cover l hb B hB hm') i j k he.1 he.2.1 he.2.2]
          rfl
      · simp [he]
  | circle =>
      have h := o.appendix_circle_mass_check l hm B hB
      simpa only [OrderObstruction.check, ScaledZWLimit.diagramCode,
        BinaryMatrixCode.decode_encode _ l.z.matrix_binary l.z.matrix_symm,
        BinaryMatrixCode.decode_encode _ l.w.matrix_binary l.w.matrix_symm, h] using Bool.not_true
  | shrinking =>
      simp only [OrderObstruction.check, o.shrinkingRadiusCheck_of_admitted l hb B hB hm', Bool.not_true]

end SequenceOrderAssignment

/-- A proof object whose branching constructor requires all admitted values. -/
inductive OrderRefutation {n : ℕ} (d : DiagramCode n) : OrderBox (ZWOrderIndex n) → Prop where
  | leaf (B) (reason : OrderObstruction n) (checked : reason.check d B = true) : OrderRefutation d B
  | trace (B C) (steps : List (SourceOrderRecord n))
      (checked : sourceOrderTraceCheck d B steps C = true)
      (rest : OrderRefutation d C) : OrderRefutation d B
  | branch (B) (slot : ZWOrderIndex n)
      (children : ∀ a ∈ B slot, OrderRefutation d (Function.update B slot {a})) : OrderRefutation d B

theorem SequenceOrderAssignment.not_admitted_refutation {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass)
    {B : OrderBox (ZWOrderIndex n)} (proof : OrderRefutation l.diagramCode B)
    (hB : B.Admits o.orderCode) : False := by
  revert hB
  induction proof with
  | leaf B reason checked =>
      intro hB
      have hn := o.orderObstruction_check_false l hb hm reason B hB
      rw [checked] at hn
      contradiction
  | trace B C steps checked rest ih =>
      intro hB
      exact ih (o.admitted_sourceOrderTrace l hb hm B hB steps C checked)
  | branch B slot children ih =>
      intro hB
      exact ih (o.orderCode slot) (hB slot) (hB.update_of_mem slot {o.orderCode slot} (by simp))

theorem impossible_of_orderRefutation {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : AdmissibleMasses mass)
    (d : DiagramCode n) (hd : l.diagramCode = d)
    (proof : OrderRefutation d (initialOrderBox d)) : False := by
  obtain ⟨φ, hφ, ⟨o⟩⟩ := exists_sequenceOrderAssignment q hb i₀ j₀ hij₀ ha
  let l' := l.comp φ hφ.tendsto_atTop
  have hp : OrderRefutation l'.diagramCode (initialOrderBox l'.diagramCode) := by
    change OrderRefutation l.diagramCode (initialOrderBox l.diagramCode)
    simpa only [hd] using proof
  exact o.not_admitted_refutation l' (fun t => hb (φ t)) hm hp
    (o.admitted_initialOrderBox l' (fun t => hb (φ t)))

end CentralConfigurations
