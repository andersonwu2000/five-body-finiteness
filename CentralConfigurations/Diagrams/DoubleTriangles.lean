import CentralConfigurations.Asymptotics.PairEstimates
import CentralConfigurations.Diagrams.MatrixRules

/-!
# Double edges and maximal strokes complete triangles

Chang (2023), Theorem 2.6, Rule 2b. A double edge bounds both coordinate
separations by epsilon. Addition preserves these two upper bounds, and the
distance equation forces the remaining pair to attain the double-edge scale.
The proof is derived from actual solution sequences; triangle closure is not
included as an assumption on their leading diagrams.
The maximal-stroke consequence also gives the first two matrix rules of
triangles (Theorem 3.4(a,b)).
-/

namespace CentralConfigurations

open Filter Asymptotics

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem double_edge_triangle (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hz₁ : l.z.force i j ≠ 0) (hw₁ : l.w.force i j ≠ 0)
    (hz₂ : l.z.force j k ≠ 0) (hw₂ : l.w.force j k ≠ 0) :
    l.z.force i k ≠ 0 ∧ l.w.force i k ≠ 0 := by
  let p₁ := ZWSystem.pairEstimateData q hb i j hij
  let p₂ := ZWSystem.pairEstimateData q hb j k hjk
  let p₃ := ZWSystem.pairEstimateData q hb i k hik
  have h₁ := p₁.small_separations_iff_double.mpr
    ⟨(l.pair_z_stroke_iff hb i j hij).mpr hz₁, (l.pair_w_stroke_iff hb i j hij).mpr hw₁⟩
  have h₂ := p₂.small_separations_iff_double.mpr
    ⟨(l.pair_z_stroke_iff hb j k hjk).mpr hz₂, (l.pair_w_stroke_iff hb j k hjk).mpr hw₂⟩
  have hz : p₃.z =O[atTop] p₃.eps := (h₁.1.add h₂.1).congr_left (fun t => by
    change ((q t).z i - (q t).z j) + ((q t).z j - (q t).z k) = (q t).z i - (q t).z k
    ring)
  have hw : p₃.w =O[atTop] p₃.eps := (h₁.2.add h₂.2).congr_left (fun t => by
    change ((q t).w i - (q t).w j) + ((q t).w j - (q t).w k) = (q t).w i - (q t).w k
    ring)
  have hf := p₃.small_separations_iff_double.mp ⟨hz, hw⟩
  exact ⟨(l.pair_z_stroke_iff hb i k hik).mp hf.1, (l.pair_w_stroke_iff hb i k hik).mp hf.2⟩

/-- The same rule in the binary matrix representation used by Algorithm I. -/
theorem double_triangle_matrix (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hz₁ : l.z.matrix i j = 1) (hw₁ : l.w.matrix i j = 1)
    (hz₂ : l.z.matrix j k = 1) (hw₂ : l.w.matrix j k = 1) :
    l.z.matrix i k = 1 ∧ l.w.matrix i k = 1 := by
  have hz₁' : l.z.force i j ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij] using hz₁
  have hw₁' : l.w.force i j ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij] using hw₁
  have hz₂' : l.z.force j k ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, hjk] using hz₂
  have hw₂' : l.w.force j k ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, hjk] using hw₂
  have h := l.double_edge_triangle hb i j k hij hjk hik hz₁' hw₁' hz₂' hw₂'
  constructor
  · simp [OneColorLimit.matrix, OneColorLimit.Incident, hik, h.1]
  · simp [OneColorLimit.matrix, OneColorLimit.Incident, hik, h.2]

/-- The consequence of Rules 2c and 2e used in Theorem 3.4(a,b): two
consecutive maximal z-strokes force a third maximal z-stroke. -/
theorem maximal_z_triangle (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hz₁ : l.z.force i j ≠ 0) (hm₁ : l.z.position i ≠ l.z.position j)
    (hz₂ : l.z.force j k ≠ 0) (hm₂ : l.z.position j ≠ l.z.position k) :
    l.z.force i k ≠ 0 ∧ l.z.position i ≠ l.z.position k := by
  let p₁ := ZWSystem.pairEstimateData q hb i j hij
  let p₂ := ZWSystem.pairEstimateData q hb j k hjk
  let p₃ := ZWSystem.pairEstimateData q hb i k hik
  have h₁ := p₁.maximal_iff_w_small.mp
    ⟨(l.pair_z_stroke_iff hb i j hij).mpr hz₁, (l.pair_z_maximal_iff hb i j hij).mpr hm₁⟩
  have h₂ := p₂.maximal_iff_w_small.mp
    ⟨(l.pair_z_stroke_iff hb j k hjk).mpr hz₂, (l.pair_z_maximal_iff hb j k hjk).mpr hm₂⟩
  have hw : p₃.w =O[atTop] (fun t => p₃.eps t ^ 2) := (h₁.1.add h₂.1).congr_left (fun t => by
    change ((q t).w i - (q t).w j) + ((q t).w j - (q t).w k) = (q t).w i - (q t).w k
    ring)
  have hf := p₃.maximal_iff_w_small.mpr ⟨hw, p₃.w_lower⟩
  exact ⟨(l.pair_z_stroke_iff hb i k hik).mp hf.1,
    (l.pair_z_maximal_iff hb i k hik).mp hf.2⟩

omit hb in
theorem different_circles_positions_ne (i j : Fin n)
    (h : l.z.matrix i i ≠ l.z.matrix j j) : l.z.position i ≠ l.z.position j := by
  intro hp
  apply h
  simp [OneColorLimit.matrix, OneColorLimit.Incident, hp]

/-- A circled center with two uncircled stroke neighbors, or the reverse
circle pattern, forces the edge between the two neighbors. -/
theorem opposite_circles_star (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hc₁ : l.z.matrix i i ≠ l.z.matrix j j)
    (hc₂ : l.z.matrix i i ≠ l.z.matrix k k)
    (he₁ : l.z.matrix i j = 1) (he₂ : l.z.matrix i k = 1) : l.z.matrix j k = 1 := by
  have hj : l.z.force j i ≠ 0 := by
    have hm : l.z.matrix j i = 1 := (l.z.matrix_symm j i).trans he₁
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, Ne.symm hij] using hm
  have hk : l.z.force i k ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, hik] using he₂
  have h := l.maximal_z_triangle hb j i k (Ne.symm hij) hik hjk hj
    (Ne.symm (l.different_circles_positions_ne i j hc₁)) hk
    (l.different_circles_positions_ne i k hc₂)
  simp [OneColorLimit.matrix, OneColorLimit.Incident, hjk, h.1]

/-- An exclusively z-colored edge and a w-stroke cannot belong to one
triangle. This is the edge-type part of Rule 2e. -/
theorem no_mixed_triangle (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hz₁ : l.z.force i j ≠ 0) (hw₁ : l.w.force i j = 0)
    (hw₂ : l.w.force j k ≠ 0)
    (he₃ : l.z.force i k ≠ 0 ∨ l.w.force i k ≠ 0) : False := by
  let p₁ := ZWSystem.pairEstimateData q hb i j hij
  let p₂ := ZWSystem.pairEstimateData q hb j k hjk
  let p₃ := ZWSystem.pairEstimateData q hb i k hik
  have hs₁ := p₁.single_z_separations ((l.pair_z_stroke_iff hb i j hij).mpr hz₁)
    ((l.pair_w_absent_iff hb i j hij).mpr hw₁)
  have hs₂ := (l.pair_w_stroke_iff hb j k hjk).mpr hw₂
  by_cases hw₃ : l.w.force i k = 0
  · have hz₃ := he₃.resolve_right (not_not.mpr hw₃)
    have hs₃ := p₃.single_z_separations ((l.pair_z_stroke_iff hb i k hik).mpr hz₃)
      ((l.pair_w_absent_iff hb i k hik).mpr hw₃)
    have ho : p₂.w =o[atTop] p₂.eps := (hs₃.2.sub hs₁.2).congr_left (fun t => by
      change ((q t).w i - (q t).w k) - ((q t).w i - (q t).w j) =
        (q t).w j - (q t).w k
      ring)
    exact ho.not_isBigO (Eventually.of_forall p₂.w_ne_zero).frequently
      (p₂.swap.stroke_z_lower hs₂)
  · have hs₃ := (l.pair_w_stroke_iff hb i k hik).mpr hw₃
    have ho : p₁.z =O[atTop] p₁.eps :=
      ((p₃.swap.stroke_w_upper hs₃).sub (p₂.swap.stroke_w_upper hs₂)).congr_left (fun t => by
        change ((q t).z i - (q t).z k) - ((q t).z j - (q t).z k) =
          (q t).z i - (q t).z j
        ring)
    exact hs₁.1.not_isBigO (Eventually.of_forall p₁.eps_ne_zero).frequently ho

theorem triangle_z_only (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hz₁ : l.z.force i j ≠ 0) (hw₁ : l.w.force i j = 0)
    (he₂ : l.z.force j k ≠ 0 ∨ l.w.force j k ≠ 0)
    (he₃ : l.z.force i k ≠ 0 ∨ l.w.force i k ≠ 0) :
    l.z.force j k ≠ 0 ∧ l.w.force j k = 0 ∧
      l.z.force i k ≠ 0 ∧ l.w.force i k = 0 := by
  have hw₂ : l.w.force j k = 0 := by
    by_contra h
    exact l.no_mixed_triangle hb i j k hij hjk hik hz₁ hw₁ h he₃
  have hw₃ : l.w.force i k = 0 := by
    by_contra h
    apply l.no_mixed_triangle hb j i k (Ne.symm hij) hik hjk
    · rw [l.z.antisymm j i]
      exact neg_ne_zero.mpr hz₁
    · rw [l.w.antisymm j i, hw₁, neg_zero]
    · exact h
    · exact he₂
  exact ⟨he₂.resolve_right (not_not.mpr hw₂), hw₂,
    he₃.resolve_right (not_not.mpr hw₃), hw₃⟩

theorem triangle_w_only (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hw₁ : l.w.force i j ≠ 0) (hz₁ : l.z.force i j = 0)
    (he₂ : l.z.force j k ≠ 0 ∨ l.w.force j k ≠ 0)
    (he₃ : l.z.force i k ≠ 0 ∨ l.w.force i k ≠ 0) :
    l.w.force j k ≠ 0 ∧ l.z.force j k = 0 ∧
      l.w.force i k ≠ 0 ∧ l.z.force i k = 0 := by
  exact (l.swapBalanced hb).triangle_z_only (fun t => (hb t).symm)
    i j k hij hjk hik hw₁ hz₁ he₂.symm he₃.symm

/-- Every triangle has three z-only edges, three w-only edges, or three
double edges. This asserts the color classification; comparability of all
three same-color separations in Rule 2e is a separate statement. -/
theorem triangle_edge_types (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (he₁ : l.z.force i j ≠ 0 ∨ l.w.force i j ≠ 0)
    (he₂ : l.z.force j k ≠ 0 ∨ l.w.force j k ≠ 0)
    (he₃ : l.z.force i k ≠ 0 ∨ l.w.force i k ≠ 0) :
    (l.z.force i j ≠ 0 ∧ l.z.force j k ≠ 0 ∧ l.z.force i k ≠ 0 ∧
      l.w.force i j = 0 ∧ l.w.force j k = 0 ∧ l.w.force i k = 0) ∨
    (l.w.force i j ≠ 0 ∧ l.w.force j k ≠ 0 ∧ l.w.force i k ≠ 0 ∧
      l.z.force i j = 0 ∧ l.z.force j k = 0 ∧ l.z.force i k = 0) ∨
    (l.z.force i j ≠ 0 ∧ l.z.force j k ≠ 0 ∧ l.z.force i k ≠ 0 ∧
      l.w.force i j ≠ 0 ∧ l.w.force j k ≠ 0 ∧ l.w.force i k ≠ 0) := by
  by_cases hz₁ : l.z.force i j = 0
  · have hw₁ := he₁.resolve_left (not_not.mpr hz₁)
    have h := l.triangle_w_only hb i j k hij hjk hik hw₁ hz₁ he₂ he₃
    exact Or.inr (Or.inl ⟨hw₁, h.1, h.2.2.1, hz₁, h.2.1, h.2.2.2⟩)
  · by_cases hw₁ : l.w.force i j = 0
    · have h := l.triangle_z_only hb i j k hij hjk hik hz₁ hw₁ he₂ he₃
      exact Or.inl ⟨hz₁, h.1, h.2.2.1, hw₁, h.2.1, h.2.2.2⟩
    · have he₁' : l.z.force j i ≠ 0 ∨ l.w.force j i ≠ 0 := Or.inl (by
        rw [l.z.antisymm j i]; exact neg_ne_zero.mpr hz₁)
      have he₃' : l.z.force k i ≠ 0 ∨ l.w.force k i ≠ 0 := by
        simpa only [l.z.antisymm k i, l.w.antisymm k i, neg_ne_zero] using he₃
      have hz₂ : l.z.force j k ≠ 0 := by
        intro hzero
        have hw₂ := he₂.resolve_left (not_not.mpr hzero)
        have h := l.triangle_w_only hb j k i hjk (Ne.symm hik) (Ne.symm hij)
          hw₂ hzero he₃' he₁'
        apply hz₁
        simpa only [l.z.antisymm j i, neg_eq_zero] using h.2.2.2
      have hw₂ : l.w.force j k ≠ 0 := by
        intro hzero
        have h := l.triangle_z_only hb j k i hjk (Ne.symm hik) (Ne.symm hij)
          hz₂ hzero he₃' he₁'
        apply hw₁
        simpa only [l.w.antisymm j i, neg_eq_zero] using h.2.2.2
      have h := l.double_edge_triangle hb i j k hij hjk hik hz₁ hw₁ hz₂ hw₂
      exact Or.inr (Or.inr ⟨hz₁, hz₂, h.1, hw₁, hw₂, h.2⟩)

end ScaledZWLimit

/-- The finite six-entry calculation in Theorem 3.4(a,b), conditional on the
proved star restriction. Every binary case is checked by Lean's kernel. -/
theorem binary_triangle_products (a b c d e f : ℕ)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (hd : d = 0 ∨ d = 1) (he : e = 0 ∨ e = 1) (hf : f = 0 ∨ f = 1)
    (hs₁ : a ≠ b → a ≠ c → d = 1 → e = 1 → f = 1)
    (hs₂ : b ≠ a → b ≠ c → d = 1 → f = 1 → e = 1)
    (hs₃ : c ≠ a → c ≠ b → e = 1 → f = 1 → d = 1) :
    (a + b + c) * (a + d + e) * (e + f + c) * (d + b + f) ≠ 16 ∧
      (a + d + e + b + f + c) * max (a + d + e) (max (d + b + f) (e + f + c)) ≠ 9 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    norm_num at *

/-- The remaining six-bit calculation in Theorem 3.4(c,d). The hypotheses
are precisely double-edge closure and the proved homogeneous triangle types. -/
theorem binary_colored_triangle_counts (a b c d e f : ℕ)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (hd : d = 0 ∨ d = 1) (he : e = 0 ∨ e = 1) (hf : f = 0 ∨ f = 1)
    (h₁ : a = 1 → d = 1 → b = 1 → e = 1 → c = 1 ∧ f = 1)
    (h₂ : a = 1 → d = 1 → c = 1 → f = 1 → b = 1 ∧ e = 1)
    (h₃ : b = 1 → e = 1 → c = 1 → f = 1 → a = 1 ∧ d = 1)
    (ht : a + d ≠ 0 → b + e ≠ 0 → c + f ≠ 0 →
      (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 0 ∧ e = 0 ∧ f = 0) ∨
      (d = 1 ∧ e = 1 ∧ f = 1 ∧ a = 0 ∧ b = 0 ∧ c = 0) ∨
      (a = 1 ∧ b = 1 ∧ c = 1 ∧ d = 1 ∧ e = 1 ∧ f = 1)) :
    (a + d) + (b + e) + (c + f) ≠ 4 ∧
    (a + d) + (b + e) + (c + f) ≠ 5 ∧
    ((a + d) * (b + e) * (c + f) * max (a + b + c) (d + e + f) = 0 ∨
      (a + d) * (b + e) * (c + f) * max (a + b + c) (d + e + f) = 3 ∨
      (a + d) * (b + e) * (c + f) * max (a + b + c) (d + e + f) = 24) := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    norm_num at *

def MonochromeTriangleRules {n : ℕ} (A : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    (A i i + A j j + A k k) * (A i i + A i j + A i k) *
        (A i k + A j k + A k k) * (A i j + A j j + A j k) ≠ 16 ∧
    (A i i + A i j + A i k + A j j + A j k + A k k) *
      max (A i i + A i j + A i k)
        (max (A i j + A j j + A j k) (A i k + A j k + A k k)) ≠ 9

def ColoredTriangleRules {n : ℕ} (A B : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
    (A i j + B i j) + (A j k + B j k) + (A i k + B i k) ≠ 4 ∧
    (A i j + B i j) + (A j k + B j k) + (A i k + B i k) ≠ 5 ∧
    ((A i j + B i j) * (A j k + B j k) * (A i k + B i k) *
        max (A i j + A j k + A i k) (B i j + B j k + B i k) = 0 ∨
      (A i j + B i j) * (A j k + B j k) * (A i k + B i k) *
        max (A i j + A j k + A i k) (B i j + B j k + B i k) = 3 ∨
      (A i j + B i j) * (A j k + B j k) * (A i k + B i k) *
        max (A i j + A j k + A i k) (B i j + B j k + B i k) = 24)

structure TriangleMatrixRules {n : ℕ} (A B : Fin n → Fin n → ℕ) : Prop where
  monochromeA : MonochromeTriangleRules A
  monochromeB : MonochromeTriangleRules B
  colored : ColoredTriangleRules A B

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

/-- Theorem 3.4(a,b), for actual leading matrices. -/
theorem first_two_triangle_rules (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    (l.z.matrix i i + l.z.matrix j j + l.z.matrix k k) *
        (l.z.matrix i i + l.z.matrix i j + l.z.matrix i k) *
        (l.z.matrix i k + l.z.matrix j k + l.z.matrix k k) *
        (l.z.matrix i j + l.z.matrix j j + l.z.matrix j k) ≠ 16 ∧
      (l.z.matrix i i + l.z.matrix i j + l.z.matrix i k + l.z.matrix j j +
        l.z.matrix j k + l.z.matrix k k) *
        max (l.z.matrix i i + l.z.matrix i j + l.z.matrix i k)
          (max (l.z.matrix i j + l.z.matrix j j + l.z.matrix j k)
            (l.z.matrix i k + l.z.matrix j k + l.z.matrix k k)) ≠ 9 := by
  apply binary_triangle_products _ _ _ _ _ _
    (l.z.matrix_binary i i) (l.z.matrix_binary j j) (l.z.matrix_binary k k)
    (l.z.matrix_binary i j) (l.z.matrix_binary i k) (l.z.matrix_binary j k)
  · exact l.opposite_circles_star hb i j k hij hik hjk
  · intro hc₁ hc₂ he₁ he₂
    apply l.opposite_circles_star hb j i k (Ne.symm hij) hjk hik hc₁ hc₂
    · exact (l.z.matrix_symm j i).trans he₁
    · exact he₂
  · intro hc₁ hc₂ he₁ he₂
    apply l.opposite_circles_star hb k i j (Ne.symm hik) (Ne.symm hjk) hij hc₁ hc₂
    · exact (l.z.matrix_symm k i).trans he₁
    · exact (l.z.matrix_symm k j).trans he₂

omit hb in
theorem matrix_edge_iff (i j : Fin n) (hij : i ≠ j) :
    l.z.matrix i j + l.w.matrix i j ≠ 0 ↔
      l.z.force i j ≠ 0 ∨ l.w.force i j ≠ 0 := by
  by_cases hz : l.z.force i j = 0 <;> by_cases hw : l.w.force i j = 0 <;>
    simp [OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw]

/-- Theorem 3.4(c,d), including non-triangular three-vertex subdiagrams. -/
theorem last_two_triangle_rules : ColoredTriangleRules l.z.matrix l.w.matrix := by
  intro i j k hij hjk hik
  apply binary_colored_triangle_counts _ _ _ _ _ _
    (l.z.matrix_binary i j) (l.z.matrix_binary j k) (l.z.matrix_binary i k)
    (l.w.matrix_binary i j) (l.w.matrix_binary j k) (l.w.matrix_binary i k)
  · exact l.double_triangle_matrix hb i j k hij hjk hik
  · intro ha hd hc hf
    exact l.double_triangle_matrix hb j i k (Ne.symm hij) hik hjk
      ((l.z.matrix_symm j i).trans ha) ((l.w.matrix_symm j i).trans hd) hc hf
  · intro hb' he hc hf
    exact l.double_triangle_matrix hb i k j hik (Ne.symm hjk) hij hc hf
      ((l.z.matrix_symm k j).trans hb') ((l.w.matrix_symm k j).trans he)
  · intro he₁ he₂ he₃
    have h := l.triangle_edge_types hb i j k hij hjk hik
      ((l.matrix_edge_iff i j hij).mp he₁) ((l.matrix_edge_iff j k hjk).mp he₂)
      ((l.matrix_edge_iff i k hik).mp he₃)
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij, hjk, hik] using h

/-- All four rules of Theorem 3.4, with (a,b) checked in both colors. -/
theorem triangleMatrixRules : TriangleMatrixRules l.z.matrix l.w.matrix where
  monochromeA := l.first_two_triangle_rules hb
  monochromeB := (l.swapBalanced hb).first_two_triangle_rules (fun t => (hb t).symm)
  colored := l.last_two_triangle_rules hb

end ScaledZWLimit
end CentralConfigurations
