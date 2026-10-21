import CentralConfigurations.Enumeration.SequenceOrderDomains

/-!
# The existential triangle update in Appendix II

TriIneqQ2 tests existence of two admitted companion levels, rather than only
their extrema. The finite filter below implements that exact test. Sequential
updates preserve the same actual assignment, including non-convex domains.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

namespace OrderBox

def exactTriangleFilter (A B C : Finset (Fin 6)) : Finset (Fin 6) :=
  A.filter fun a => ∃ b ∈ B, ∃ c ∈ C, OrderTriangle a b c

theorem mem_exactTriangleFilter {A B C : Finset (Fin 6)} {a b c : Fin 6}
    (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C) (ht : OrderTriangle a b c) :
    a ∈ exactTriangleFilter A B C :=
  Finset.mem_filter.mpr ⟨ha, b, hb, c, hc, ht⟩

theorem exactTriangleFilter_subset_triangleFilter (A B C : Finset (Fin 6)) :
    exactTriangleFilter A B C ⊆ triangleFilter A B C := by
  intro a ha
  obtain ⟨ha, b, hb, c, hc, ht⟩ := Finset.mem_filter.mp ha
  exact mem_triangleFilter ha hb hc ht

variable {ι : Type*} [DecidableEq ι]

def exactTriangleAt (B : OrderBox ι) (x y z : ι) : OrderBox ι :=
  Function.update B x (exactTriangleFilter (B x) (B y) (B z))

theorem Admits.exactTriangleAt {B : OrderBox ι} {k : ι → Fin 6}
    (h : B.Admits k) (x y z : ι) (ht : OrderTriangle (k x) (k y) (k z)) :
    (exactTriangleAt B x y z).Admits k :=
  h.update_of_mem x _ (mem_exactTriangleFilter (h x) (h y) (h z) ht)

def exactTriangleStep (B : OrderBox ι) (x y z : ι) : OrderBox ι :=
  let B₁ := exactTriangleAt B x y z
  let B₂ := exactTriangleAt B₁ y x z
  exactTriangleAt B₂ z x y

theorem Admits.exactTriangleStep {B : OrderBox ι} {k : ι → Fin 6}
    (h : B.Admits k) (x y z : ι) (ht : OrderTriangle (k x) (k y) (k z)) :
    (exactTriangleStep B x y z).Admits k :=
  ((h.exactTriangleAt x y z ht).exactTriangleAt y x z ht.swap_left).exactTriangleAt
    z x y ht.rotate

end OrderBox

def appendixPositionTriangle {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i j : Fin n) : OrderBox (ZWOrderIndex n) :=
  if i ≠ j then OrderBox.exactTriangleStep B (zwOrderSlot color i i)
    (zwOrderSlot color i j) (zwOrderSlot color j j) else B

def appendixSeparationTriangle {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i j k : Fin n) : OrderBox (ZWOrderIndex n) :=
  if i ≠ j ∧ j ≠ k ∧ i ≠ k then
    OrderBox.exactTriangleStep B (zwOrderSlot color i j)
      (zwOrderSlot color j k) (zwOrderSlot color i k) else B

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

theorem admitted_appendixPositionTriangle (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color : Fin 2) (i j : Fin n) :
    (appendixPositionTriangle B color i j).Admits o.orderCode := by
  unfold appendixPositionTriangle
  split_ifs with hij
  · apply hB.exactTriangleStep
    fin_cases color
    · change OrderTriangle (o.orderCode (zwOrderSlot 0 i i))
        (o.orderCode (zwOrderSlot 0 i j)) (o.orderCode (zwOrderSlot 0 j j))
      simpa only [orderCode_z] using (o.z_position_triangle i j hij).swap_left
    · change OrderTriangle (o.orderCode (zwOrderSlot 1 i i))
        (o.orderCode (zwOrderSlot 1 i j)) (o.orderCode (zwOrderSlot 1 j j))
      simpa only [orderCode_w] using (o.w_position_triangle i j hij).swap_left
  · exact hB

theorem admitted_appendixSeparationTriangle (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color : Fin 2) (i j k : Fin n) :
    (appendixSeparationTriangle B color i j k).Admits o.orderCode := by
  unfold appendixSeparationTriangle
  split_ifs with h
  · apply hB.exactTriangleStep
    fin_cases color
    · change OrderTriangle (o.orderCode (zwOrderSlot 0 i j))
        (o.orderCode (zwOrderSlot 0 j k)) (o.orderCode (zwOrderSlot 0 i k))
      have ht := o.z_separation_triangle j i k h.1.symm h.2.1 h.2.2.symm
      simpa only [orderCode_z, o.z_symm j i, o.z_symm k i] using ht
    · change OrderTriangle (o.orderCode (zwOrderSlot 1 i j))
        (o.orderCode (zwOrderSlot 1 j k)) (o.orderCode (zwOrderSlot 1 i k))
      have ht := o.w_separation_triangle j i k h.1.symm h.2.1 h.2.2.symm
      simpa only [orderCode_w, o.w_symm j i, o.w_symm k i] using ht
  · exact hB

end SequenceOrderAssignment

end CentralConfigurations
