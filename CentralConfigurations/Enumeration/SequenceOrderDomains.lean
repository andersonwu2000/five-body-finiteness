import CentralConfigurations.Enumeration.OrderDomains
import CentralConfigurations.Enumeration.NormalizedSearch
import CentralConfigurations.Diagrams.InitialOrderLevels

/-!
# Actual singular sequences are covered by the Section 4 domains

Upper-triangular storage makes matrix symmetry automatic. The first index
chooses z or w. The initial box is Proposition 4.4; the three consecutive
triangle updates are Proposition 4.5. Coverage quantifies over all further
strict subsequences carrying fixed levels, as in Definition 4.2.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

abbrev ZWOrderIndex (n : ℕ) := Fin 2 × UpperIndex n

def zwOrderSlot {n : ℕ} (color : Fin 2) (i j : Fin n) : ZWOrderIndex n :=
  (color, upperIndex i j)

def initialOrderEntry (diagonal own other : Bool) : Finset (Fin 6) :=
  if diagonal then
    if own then {5} else {0, 1, 2, 3, 4}
  else if own then
    if other then {3} else {4, 5}
  else if other then {1, 2} else {2, 3, 4, 5}

def initialOrderBox {n : ℕ} (d : DiagramCode n) : OrderBox (ZWOrderIndex n) :=
  fun p => initialOrderEntry (decide (p.2.1.1 = p.2.1.2))
    (![d.1 p.2, d.2 p.2] p.1) (![d.2 p.2, d.1 p.2] p.1)

noncomputable def zwOrderValue {n : ℕ} {mass : Fin n → ℂ} (q : ZWSystem ℂ n mass)
    (p : ZWOrderIndex n) : ℂ :=
  ![q.zOrderValue p.2.1.1 p.2.1.2, q.wOrderValue p.2.1.1 p.2.1.2] p.1

/-- Fixed z/w levels alone; no hypothesis about fixed distance levels. -/
def HasZWOrderCode {n : ℕ} {mass : Fin n → ℂ} (q : ℕ → ZWSystem ℂ n mass)
    (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (k : ZWOrderIndex n → Fin 6) : Prop :=
  ∀ p, HasOrderLevel (ZWSystem.orderPositionScales q i₀ j₀ hij₀ ha)
    (fun t => zwOrderValue (q t) p) (k p)

theorem HasZWOrderCode.comp {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
    {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {k : ZWOrderIndex n → Fin 6} (h : HasZWOrderCode q i₀ j₀ hij₀ ha k)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    HasZWOrderCode (q ∘ φ) i₀ j₀ hij₀ (ha.comp hφ.tendsto_atTop) k :=
  fun p => (h p).comp φ hφ.tendsto_atTop

theorem symmetric_upperIndex {n : ℕ} {α : Type*} (A : Fin n → Fin n → α)
    (hs : ∀ i j, A i j = A j i) (i j : Fin n) :
    A (upperIndex i j).1.1 (upperIndex i j).1.2 = A i j := by
  by_cases hij : i ≤ j
  · simp only [upperIndex, min_eq_left hij, max_eq_right hij]
  · have hji := le_of_lt (lt_of_not_ge hij)
    simpa only [upperIndex, min_eq_right hji, max_eq_left hji] using hs j i

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

def orderCode : ZWOrderIndex n → Fin 6 :=
  fun p => ![o.z p.2.1.1 p.2.1.2, o.w p.2.1.1 p.2.1.2] p.1

theorem hasZWOrderCode : HasZWOrderCode q i₀ j₀ hij₀ ha o.orderCode := by
  rintro ⟨c, p⟩
  fin_cases c
  · exact o.z_level p.1.1 p.1.2
  · exact o.w_level p.1.1 p.1.2

@[simp] theorem orderCode_z (i j : Fin n) : o.orderCode (zwOrderSlot 0 i j) = o.z i j :=
  symmetric_upperIndex o.z o.z_symm i j

@[simp] theorem orderCode_w (i j : Fin n) : o.orderCode (zwOrderSlot 1 i j) = o.w i j :=
  symmetric_upperIndex o.w o.w_symm i j

variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem z_mem_initialEntry (i j : Fin n) :
    o.z i j ∈ initialOrderEntry (decide (i = j))
      (decide (l.z.matrix i j = 1)) (decide (l.w.matrix i j = 1)) := by
  by_cases hij : i = j
  · subst j
    by_cases hc : l.z.position i = 0
    · have hn : o.z i i ≠ 5 := fun h => (o.z_diagonal_five_iff l i).mp h hc
      have hk : o.z i i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 6)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        have hbnd := (o.z i i).isLt
        omega
      simpa [initialOrderEntry, OneColorLimit.matrix, OneColorLimit.Incident, hc] using hk
    · have hk := (o.z_diagonal_five_iff l i).mpr hc
      simp [initialOrderEntry, OneColorLimit.matrix, OneColorLimit.Incident, hc, hk]
  · by_cases hz : l.z.force i j = 0
    · by_cases hw : l.w.force i j = 0
      · have h := (o.absent_edge_levels l hb i j hij hz hw).1
        have hk : o.z i j ∈ ({2, 3, 4, 5} : Finset (Fin 6)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          have hbnd := (o.z i j).isLt
          omega
        simpa [initialOrderEntry, OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw] using hk
      · have h := o.single_w_levels l hb i j hij hz hw
        have hk : o.z i j ∈ ({1, 2} : Finset (Fin 6)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        simpa [initialOrderEntry, OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw] using hk
    · by_cases hw : l.w.force i j = 0
      · have h := (o.single_z_levels l hb i j hij hz hw).1
        have hk : o.z i j ∈ ({4, 5} : Finset (Fin 6)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          have hbnd := (o.z i j).isLt
          omega
        simpa [initialOrderEntry, OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw] using hk
      · have hk := (o.double_edge_levels l hb i j hij hz hw).1
        simp [initialOrderEntry, OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw, hk]

theorem w_mem_initialEntry (i j : Fin n) :
    o.w i j ∈ initialOrderEntry (decide (i = j))
      (decide (l.w.matrix i j = 1)) (decide (l.z.matrix i j = 1)) := by
  by_cases hij : i = j
  · subst j
    by_cases hc : l.w.position i = 0
    · have hn : o.w i i ≠ 5 := fun h => (o.w_diagonal_five_iff l i).mp h hc
      have hk : o.w i i ∈ ({0, 1, 2, 3, 4} : Finset (Fin 6)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        have hbnd := (o.w i i).isLt
        omega
      simpa [initialOrderEntry, OneColorLimit.matrix, OneColorLimit.Incident, hc] using hk
    · have hk := (o.w_diagonal_five_iff l i).mpr hc
      simp [initialOrderEntry, OneColorLimit.matrix, OneColorLimit.Incident, hc, hk]
  · by_cases hw : l.w.force i j = 0
    · by_cases hz : l.z.force i j = 0
      · have h := (o.absent_edge_levels l hb i j hij hz hw).2
        have hk : o.w i j ∈ ({2, 3, 4, 5} : Finset (Fin 6)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          have hbnd := (o.w i j).isLt
          omega
        simpa [initialOrderEntry, OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw] using hk
      · have h := o.single_z_levels l hb i j hij hz hw
        have hk : o.w i j ∈ ({1, 2} : Finset (Fin 6)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
        simpa [initialOrderEntry, OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw] using hk
    · by_cases hz : l.z.force i j = 0
      · have h := (o.single_w_levels l hb i j hij hz hw).2.2
        have hk : o.w i j ∈ ({4, 5} : Finset (Fin 6)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton]
          have hbnd := (o.w i j).isLt
          omega
        simpa [initialOrderEntry, OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw] using hk
      · have hk := (o.double_edge_levels l hb i j hij hz hw).2.1
        simp [initialOrderEntry, OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw, hk]

/-- Proposition 4.4, as membership of a computable box from the diagram. -/
theorem admitted_initialOrderBox : (initialOrderBox l.diagramCode).Admits o.orderCode := by
  rintro ⟨c, ⟨⟨i, j⟩, hle⟩⟩
  fin_cases c
  · exact o.z_mem_initialEntry l hb i j
  · exact o.w_mem_initialEntry l hb i j

omit hb in
/-- Proposition 4.5, for either color and every admissible third vertex. -/
theorem admitted_coordinateTriangleStep (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color : Fin 2) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) :
    (OrderBox.coordinateTriangleStep B (zwOrderSlot color i j)
      (zwOrderSlot color i k) (zwOrderSlot color k j)
      (zwOrderSlot color i i) (zwOrderSlot color j j)).Admits o.orderCode := by
  apply hB.coordinateTriangleStep
  · fin_cases color
    · change OrderTriangle (o.orderCode (zwOrderSlot 0 i j))
        (o.orderCode (zwOrderSlot 0 i k)) (o.orderCode (zwOrderSlot 0 k j))
      simpa only [orderCode_z] using o.z_separation_triangle i j k hij hik hkj
    · change OrderTriangle (o.orderCode (zwOrderSlot 1 i j))
        (o.orderCode (zwOrderSlot 1 i k)) (o.orderCode (zwOrderSlot 1 k j))
      simpa only [orderCode_w] using o.w_separation_triangle i j k hij hik hkj
  · fin_cases color
    · change OrderTriangle (o.orderCode (zwOrderSlot 0 i j))
        (o.orderCode (zwOrderSlot 0 i i)) (o.orderCode (zwOrderSlot 0 j j))
      simpa only [orderCode_z] using o.z_position_triangle i j hij
    · change OrderTriangle (o.orderCode (zwOrderSlot 1 i j))
        (o.orderCode (zwOrderSlot 1 i i)) (o.orderCode (zwOrderSlot 1 j j))
      simpa only [orderCode_w] using o.w_position_triangle i j hij

end SequenceOrderAssignment

theorem HasZWOrderCode.eq_orderCode {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
    {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {k : ZWOrderIndex n → Fin 6} (h : HasZWOrderCode q i₀ j₀ hij₀ ha k)
    (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha) : k = o.orderCode := by
  funext p
  exact (h p).unique (o.hasZWOrderCode p)

/-- Definition 4.2 with its universal quantifier over further subsequences.
Every box uses symmetric storage, and its entries are finite sets of levels. -/
def ZWOrderCoverage {n : ℕ} {mass : Fin n → ℂ} (q : ℕ → ZWSystem ℂ n mass)
    (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (C : Finset (OrderBox (ZWOrderIndex n))) : Prop :=
  ∀ (φ : ℕ → ℕ) (hφ : StrictMono φ) (k : ZWOrderIndex n → Fin 6),
    HasZWOrderCode (q ∘ φ) i₀ j₀ hij₀ (ha.comp hφ.tendsto_atTop) k →
      OrderBox.CoveredBy C k

/-- Requiring fixed distances in an intermediate proof loses no z/w order
assignment: refine again, and uniqueness preserves the previously fixed levels. -/
theorem zwOrderCoverage_iff_joint {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (C : Finset (OrderBox (ZWOrderIndex n))) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha C ↔
      ∀ (φ : ℕ → ℕ) (hφ : StrictMono φ)
        (o : SequenceOrderAssignment (q ∘ φ) i₀ j₀ hij₀ (ha.comp hφ.tendsto_atTop)),
          OrderBox.CoveredBy C o.orderCode := by
  constructor
  · intro h φ hφ o
    exact h φ hφ o.orderCode o.hasZWOrderCode
  · intro h φ hφ k hk
    obtain ⟨ψ, hψ, ⟨o⟩⟩ := exists_sequenceOrderAssignment (q ∘ φ)
      (fun t => hb (φ t)) i₀ j₀ hij₀ (ha.comp hφ.tendsto_atTop)
    rw [(hk.comp ψ hψ).eq_orderCode o]
    exact h (φ ∘ ψ) (hφ.comp hψ) o

theorem initialOrderBox_covers_sequence {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha {initialOrderBox l.diagramCode} := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  exact ⟨initialOrderBox l.diagramCode, Finset.mem_singleton_self _,
    o.admitted_initialOrderBox (l.comp φ hφ.tendsto_atTop) (fun t => hb (φ t))⟩

theorem not_empty_order_coverage {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) :
    ¬ ZWOrderCoverage q i₀ j₀ hij₀ ha ∅ := by
  intro hc
  obtain ⟨φ, hφ, ⟨o⟩⟩ := exists_sequenceOrderAssignment q hb i₀ j₀ hij₀ ha
  obtain ⟨B, hB, _⟩ := hc φ hφ o.orderCode o.hasZWOrderCode
  exact Finset.notMem_empty _ hB

namespace ZWOrderCoverage

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable {C D : Finset (OrderBox (ZWOrderIndex n))}

theorem pairwiseIntersections (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (hD : ZWOrderCoverage q i₀ j₀ hij₀ ha D) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (OrderBox.pairwiseIntersections C D) := by
  intro φ hφ k hk
  exact (OrderBox.covered_pairwiseIntersections_iff C D k).mpr
    ⟨hC φ hφ k hk, hD φ hφ k hk⟩

theorem pruneEmpty (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (OrderBox.pruneEmpty C) := by
  intro φ hφ k hk
  exact (OrderBox.covered_pruneEmpty_iff C k).mpr (hC φ hφ k hk)

theorem branchFamilyAt (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C) (i : ZWOrderIndex n) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (OrderBox.branchFamilyAt C i) := by
  intro φ hφ k hk
  exact (OrderBox.covered_branchFamilyAt_iff C i k).mpr (hC φ hφ k hk)

theorem coordinateTriangleStep (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (color : Fin 2) (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha
      (C.image fun B => OrderBox.coordinateTriangleStep B (zwOrderSlot color i j)
        (zwOrderSlot color i k) (zwOrderSlot color k j)
        (zwOrderSlot color i i) (zwOrderSlot color j j)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_coordinateTriangleStep B ho color i j k hij hik hkj⟩

end ZWOrderCoverage

end CentralConfigurations
