import CentralConfigurations.Enumeration.SequenceOrderDomains
import CentralConfigurations.Diagrams.TriangleOrders

/-!
# Proposition 4.6: all edges of an actual triangle have equal levels

The analytic input is Theorem 2.6's two-sided comparison of the coordinate
separations. Equalizing the three finite domains therefore preserves every
actual level assignment, and hence the full subsequence coverage property.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem edge_triangle_levels_equal (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (he₁ : l.z.force i j ≠ 0 ∨ l.w.force i j ≠ 0)
    (he₂ : l.z.force j k ≠ 0 ∨ l.w.force j k ≠ 0)
    (he₃ : l.z.force i k ≠ 0 ∨ l.w.force i k ≠ 0) :
    o.z i j = o.z j k ∧ o.z i j = o.z i k ∧
      o.w i j = o.w j k ∧ o.w i j = o.w i k := by
  have h := l.triangle_separation_orders hb i j k hij hjk hik he₁ he₂ he₃
  exact ⟨((o.z_separation_level i j hij).of_isTheta h.1).unique (o.z_separation_level j k hjk),
    ((o.z_separation_level i j hij).of_isTheta h.2.1).unique (o.z_separation_level i k hik),
    ((o.w_separation_level i j hij).of_isTheta h.2.2.1).unique (o.w_separation_level j k hjk),
    ((o.w_separation_level i j hij).of_isTheta h.2.2.2).unique (o.w_separation_level i k hik)⟩

theorem admitted_equalizeTriangle (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color : Fin 2) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (he₁ : l.z.force i j ≠ 0 ∨ l.w.force i j ≠ 0)
    (he₂ : l.z.force j k ≠ 0 ∨ l.w.force j k ≠ 0)
    (he₃ : l.z.force i k ≠ 0 ∨ l.w.force i k ≠ 0) :
    (OrderBox.equalizeTriple B (zwOrderSlot color i j)
      (zwOrderSlot color j k) (zwOrderSlot color i k)).Admits o.orderCode := by
  have h := o.edge_triangle_levels_equal l hb i j k hij hjk hik he₁ he₂ he₃
  apply hB.equalizeTriple
  · fin_cases color
    · change o.orderCode (zwOrderSlot 0 i j) = o.orderCode (zwOrderSlot 0 j k)
      simpa only [orderCode_z] using h.1
    · change o.orderCode (zwOrderSlot 1 i j) = o.orderCode (zwOrderSlot 1 j k)
      simpa only [orderCode_w] using h.2.2.1
  · fin_cases color
    · change o.orderCode (zwOrderSlot 0 i j) = o.orderCode (zwOrderSlot 0 i k)
      simpa only [orderCode_z] using h.2.1
    · change o.orderCode (zwOrderSlot 1 i j) = o.orderCode (zwOrderSlot 1 i k)
      simpa only [orderCode_w] using h.2.2.2

end SequenceOrderAssignment

theorem ZWOrderCoverage.equalizeTriangle {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (color : Fin 2) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (he₁ : l.z.force i j ≠ 0 ∨ l.w.force i j ≠ 0)
    (he₂ : l.z.force j k ≠ 0 ∨ l.w.force j k ≠ 0)
    (he₃ : l.z.force i k ≠ 0 ∨ l.w.force i k ≠ 0) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha
      (C.image fun B => OrderBox.equalizeTriple B (zwOrderSlot color i j)
        (zwOrderSlot color j k) (zwOrderSlot color i k)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_equalizeTriangle (l.comp φ hφ.tendsto_atTop) (fun t => hb (φ t))
      B ho color i j k hij hjk hik he₁ he₂ he₃⟩

end CentralConfigurations
