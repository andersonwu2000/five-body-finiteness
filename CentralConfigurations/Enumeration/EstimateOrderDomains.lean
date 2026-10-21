import CentralConfigurations.Enumeration.DistanceOrderDomains

/-!
# Proposition 4.7(a) and Appendix II's Estimate operation

The edge rule is the printed complementary-level intersection. For absent
edges this file implements the maximum-domain rule used by Appendix II.
The printed universal quantifier over the opposite domain is different and
is not assumed here. Every operation preserves the full subsequence coverage.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

def absentOrderThreshold (k : ℕ) : ℕ := 6 - 2 * (k / 2)

theorem absentOrderThreshold_antitone : Antitone absentOrderThreshold := by
  intro a b hab
  have h := Nat.div_le_div_right hab (c := 2)
  unfold absentOrderThreshold
  omega

theorem edgeDistanceTable_level_sum : ∀ z w r : Fin 6,
    r ∈ edgeDistanceTable z w → z.val + w.val = 6 := by decide

theorem absentDistanceTable_thresholds : ∀ z w r : Fin 6,
    r ∈ absentDistanceTable z w →
      absentOrderThreshold w.val ≤ z.val ∧ absentOrderThreshold z.val ≤ w.val := by decide

namespace OrderBox

def estimateFilter (edge : Bool) (A B : Finset (Fin 6)) : Finset (Fin 6) :=
  if edge then A.filter (fun a => ∃ b ∈ B, a.val + b.val = 6)
  else A.filter (fun a => absentOrderThreshold (B.sup Fin.val) ≤ a.val)

theorem estimateFilter_subset (edge : Bool) (A B : Finset (Fin 6)) :
    estimateFilter edge A B ⊆ A := by
  cases edge <;> exact Finset.filter_subset _ _

theorem mem_estimateFilter {edge : Bool} {A B : Finset (Fin 6)} {a b r : Fin 6}
    (ha : a ∈ A) (hb : b ∈ B) (hr : r ∈ distanceOrderTable edge a b) :
    a ∈ estimateFilter edge A B := by
  cases edge
  · apply Finset.mem_filter.mpr
    exact ⟨ha, (absentOrderThreshold_antitone (Finset.le_sup (f := Fin.val) hb)).trans
      (absentDistanceTable_thresholds a b r hr).1⟩
  · exact Finset.mem_filter.mpr ⟨ha, b, hb, edgeDistanceTable_level_sum a b r hr⟩

variable {ι : Type*} [DecidableEq ι]

def estimateRefineAt (B : OrderBox ι) (x y : ι) (edge : Bool) : OrderBox ι :=
  Function.update B x (estimateFilter edge (B x) (B y))

theorem estimateRefineAt_refines (B : OrderBox ι) (x y : ι) (edge : Bool) :
    (estimateRefineAt B x y edge).Refines B := by
  intro i
  by_cases hi : i = x
  · subst i
    simpa only [estimateRefineAt, Function.update_self] using estimateFilter_subset edge (B x) (B y)
  · simp only [estimateRefineAt, Function.update_of_ne hi]
    exact Finset.Subset.refl _

theorem Admits.estimateRefineAt {B : OrderBox ι} {k : ι → Fin 6}
    (h : B.Admits k) (x y : ι) (edge : Bool) (r : Fin 6)
    (hr : r ∈ distanceOrderTable edge (k x) (k y)) :
    (estimateRefineAt B x y edge).Admits k :=
  h.update_of_mem x _ (mem_estimateFilter (h x) (h y) hr)

def estimatePairStep (B : OrderBox ι) (x y : ι) (edge : Bool) : OrderBox ι :=
  estimateRefineAt (estimateRefineAt B x y edge) y x edge

theorem Admits.estimatePairStep {B : OrderBox ι} {k : ι → Fin 6}
    (h : B.Admits k) (x y : ι) (edge : Bool) (r : Fin 6)
    (hr : r ∈ distanceOrderTable edge (k x) (k y)) :
    (estimatePairStep B x y edge).Admits k := by
  have h₁ := h.estimateRefineAt x y edge r hr
  apply h₁.estimateRefineAt y x edge r
  rwa [distanceOrderTable_symm]

theorem estimatePairStep_refines (B : OrderBox ι) (x y : ι) (edge : Bool) :
    (estimatePairStep B x y edge).Refines B := by
  intro i
  exact (estimateRefineAt_refines _ y x edge i).trans (estimateRefineAt_refines B x y edge i)

end OrderBox

def estimateDiagramPair {n : ℕ} (d : DiagramCode n)
    (B : OrderBox (ZWOrderIndex n)) (p : StrictUpperIndex n) : OrderBox (ZWOrderIndex n) :=
  OrderBox.estimatePairStep B (zwOrderSlot 0 p.1.1 p.1.2) (zwOrderSlot 1 p.1.1 p.1.2)
    (d.1 (upperIndex p.1.1 p.1.2) || d.2 (upperIndex p.1.1 p.1.2))

def estimateDiagramSweep {n : ℕ} (d : DiagramCode n) (pairs : List (StrictUpperIndex n))
    (B : OrderBox (ZWOrderIndex n)) : OrderBox (ZWOrderIndex n) :=
  pairs.foldl (estimateDiagramPair d) B

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem admitted_estimateDiagramPair (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (p : StrictUpperIndex n) :
    (estimateDiagramPair l.diagramCode B p).Admits o.orderCode := by
  apply hB.estimatePairStep _ _ _ (o.radius p.1.1 p.1.2)
  simpa only [orderCode_z, orderCode_w, ScaledZWLimit.diagramCode,
    BinaryMatrixCode.encode, upperIndex, min_eq_left p.2.le, max_eq_right p.2.le]
    using o.mem_distanceOrderTable_matrix l hb p.1.1 p.1.2 p.2.ne

theorem admitted_estimateDiagramSweep (pairs : List (StrictUpperIndex n))
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    (estimateDiagramSweep l.diagramCode pairs B).Admits o.orderCode := by
  induction pairs generalizing B with
  | nil => exact hB
  | cons p pairs ih =>
    exact ih _ (o.admitted_estimateDiagramPair l hb B hB p)

end SequenceOrderAssignment

theorem ZWOrderCoverage.estimateDiagramSweep {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (pairs : List (StrictUpperIndex n)) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (C.image (estimateDiagramSweep l.diagramCode pairs)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_estimateDiagramSweep (l.comp φ hφ.tendsto_atTop) (fun t => hb (φ t)) pairs B ho⟩

end CentralConfigurations
