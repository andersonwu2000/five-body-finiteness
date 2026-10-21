import CentralConfigurations.Diagrams.TriangleOrders

/-!
# Quadrilateral restrictions

Chang (2023), Theorem 3.5. The first rule follows from the geometric closure
step of Rule 2f: five strokes on four vertices force the sixth stroke.
-/

namespace CentralConfigurations

open Filter Asymptotics

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

/-- The four-vertex closure step behind Rule 2f, in one color. -/
theorem five_z_strokes (i j k r : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hir : i ≠ r)
    (hjk : j ≠ k) (hjr : j ≠ r) (hkr : k ≠ r)
    (h₀ : l.z.force i j ≠ 0)
    (h₁ : l.z.force i k ≠ 0) (h₂ : l.z.force j k ≠ 0)
    (h₃ : l.z.force i r ≠ 0) (h₄ : l.z.force j r ≠ 0) : l.z.force k r ≠ 0 := by
  have hk := l.z_triangle_orders hb i j k hij hjk hik h₀ h₂ h₁
  have hr := l.z_triangle_orders hb i j r hij hjr hir h₀ h₄ h₃
  let p := ZWSystem.pairEstimateData q hb k r hkr
  let s := ZWSystem.pairEstimateData q hb i j hij
  have hz : p.z =O[atTop] s.z := (hr.2.1.2.sub hk.2.1.2).congr_left (fun t => by
    change ((q t).z i - (q t).z r) - ((q t).z i - (q t).z k) = (q t).z k - (q t).z r
    ring)
  have hw : p.w =O[atTop] s.w := (hr.2.2.2.2.sub hk.2.2.2.2).congr_left (fun t => by
    change ((q t).w i - (q t).w r) - ((q t).w i - (q t).w k) = (q t).w k - (q t).w r
    ring)
  have hs := (l.pair_z_stroke_iff hb i j hij).mpr h₀
  exact (l.pair_z_stroke_iff hb k r hkr).mp
    ⟨p.zForce_upper, hs.2.trans (p.force_reverse_bound s hz hw)⟩

theorem five_z_entries (i j k r : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hir : i ≠ r)
    (hjk : j ≠ k) (hjr : j ≠ r) (hkr : k ≠ r)
    (h₀ : l.z.matrix i j = 1)
    (h₁ : l.z.matrix i k = 1) (h₂ : l.z.matrix j k = 1)
    (h₃ : l.z.matrix i r = 1) (h₄ : l.z.matrix j r = 1) : l.z.matrix k r = 1 := by
  have h := l.five_z_strokes hb i j k r hij hik hir hjk hjr hkr
    (by simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij] using h₀)
    (by simpa [OneColorLimit.matrix, OneColorLimit.Incident, hik] using h₁)
    (by simpa [OneColorLimit.matrix, OneColorLimit.Incident, hjk] using h₂)
    (by simpa [OneColorLimit.matrix, OneColorLimit.Incident, hir] using h₃)
    (by simpa [OneColorLimit.matrix, OneColorLimit.Incident, hjr] using h₄)
  simp [OneColorLimit.matrix, OneColorLimit.Incident, hkr, h]

end ScaledZWLimit

theorem binary_six_sum_ne_five (a b c d e f : ℕ)
    (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) (hc : c = 0 ∨ c = 1)
    (hd : d = 0 ∨ d = 1) (he : e = 0 ∨ e = 1) (hf : f = 0 ∨ f = 1)
    (h₁ : b = 1 → c = 1 → d = 1 → e = 1 → f = 1 → a = 1)
    (h₂ : a = 1 → c = 1 → d = 1 → e = 1 → f = 1 → b = 1)
    (h₃ : a = 1 → b = 1 → d = 1 → e = 1 → f = 1 → c = 1)
    (h₄ : a = 1 → b = 1 → c = 1 → e = 1 → f = 1 → d = 1)
    (h₅ : a = 1 → b = 1 → c = 1 → d = 1 → f = 1 → e = 1)
    (h₆ : a = 1 → b = 1 → c = 1 → d = 1 → e = 1 → f = 1) :
    a + b + c + d + e + f ≠ 5 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> rcases hc with rfl | rfl <;>
    rcases hd with rfl | rfl <;> rcases he with rfl | rfl <;> rcases hf with rfl | rfl <;>
    norm_num at *

def FirstQuadrilateralRule {n : ℕ} (A : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j k r, i ≠ j → i ≠ k → i ≠ r → j ≠ k → j ≠ r → k ≠ r →
    A i j + A i k + A i r + A j k + A j r + A k r ≠ 5

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

/-- Theorem 3.5(a), with all six placements of the potentially missing edge. -/
theorem first_quadrilateral_rule : FirstQuadrilateralRule l.z.matrix := by
  intro i j k r hij hik hir hjk hjr hkr
  apply binary_six_sum_ne_five _ _ _ _ _ _
    (l.z.matrix_binary i j) (l.z.matrix_binary i k) (l.z.matrix_binary i r)
    (l.z.matrix_binary j k) (l.z.matrix_binary j r) (l.z.matrix_binary k r)
  · intro b c d e f
    exact l.five_z_entries hb k r i j hkr (Ne.symm hik) (Ne.symm hjk)
      (Ne.symm hir) (Ne.symm hjr) hij f
      ((l.z.matrix_symm k i).trans b) ((l.z.matrix_symm r i).trans c)
      ((l.z.matrix_symm k j).trans d) ((l.z.matrix_symm r j).trans e)
  · intro a c d e f
    exact l.five_z_entries hb j r i k hjr (Ne.symm hij) hjk (Ne.symm hir) (Ne.symm hkr) hik e
      ((l.z.matrix_symm j i).trans a) ((l.z.matrix_symm r i).trans c)
      d ((l.z.matrix_symm r k).trans f)
  · intro a b d e f
    exact l.five_z_entries hb j k i r hjk (Ne.symm hij) hjr (Ne.symm hik) hkr hir d
      ((l.z.matrix_symm j i).trans a) ((l.z.matrix_symm k i).trans b) e f
  · intro a b c e f
    exact l.five_z_entries hb i r j k hir hij hik (Ne.symm hjr) (Ne.symm hkr) hjk c
      a ((l.z.matrix_symm r j).trans e) b ((l.z.matrix_symm r k).trans f)
  · intro a b c d f
    exact l.five_z_entries hb i k j r hik hij hir (Ne.symm hjk) hkr hjr b
      a ((l.z.matrix_symm k j).trans d) c f
  · intro a b c d e
    exact l.five_z_entries hb i j k r hij hik hir hjk hjr hkr a b d c e

omit hb in
theorem edge_symm (i j : Fin n)
    (h : l.z.force i j ≠ 0 ∨ l.w.force i j ≠ 0) :
    l.z.force j i ≠ 0 ∨ l.w.force j i ≠ 0 := by
  simpa only [l.z.antisymm j i, l.w.antisymm j i, neg_ne_zero] using h

/-- Rule 2g: a z-only side forces the opposite side of a quadrilateral
to be z-only. The four cases use sums of large/small separations, including
the distance obstruction on a diagonal when both colors are small there. -/
theorem quadrilateral_z_only_opposite (i j k r : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hir : i ≠ r)
    (hjk : j ≠ k) (hjr : j ≠ r) (hkr : k ≠ r)
    (hz₁ : l.z.force i j ≠ 0) (hw₁ : l.w.force i j = 0)
    (he₂ : l.z.force j k ≠ 0 ∨ l.w.force j k ≠ 0)
    (he₃ : l.z.force k r ≠ 0 ∨ l.w.force k r ≠ 0)
    (he₄ : l.z.force i r ≠ 0 ∨ l.w.force i r ≠ 0) :
    l.z.force k r ≠ 0 ∧ l.w.force k r = 0 := by
  have hw₃ : l.w.force k r = 0 := by
    by_contra hw₃
    let p₁ := ZWSystem.pairEstimateData q hb i j hij
    let p₂ := ZWSystem.pairEstimateData q hb j k hjk
    let p₃ := ZWSystem.pairEstimateData q hb k r hkr
    let p₄ := ZWSystem.pairEstimateData q hb i r hir
    have hs₁ := p₁.single_z_separations ((l.pair_z_stroke_iff hb i j hij).mpr hz₁)
      ((l.pair_w_absent_iff hb i j hij).mpr hw₁)
    have hf₃ := (l.pair_w_stroke_iff hb k r hkr).mpr hw₃
    by_cases hw₂ : l.w.force j k = 0
    · have hz₂ := he₂.resolve_right (not_not.mpr hw₂)
      have hs₂ := p₂.single_z_separations ((l.pair_z_stroke_iff hb j k hjk).mpr hz₂)
        ((l.pair_w_absent_iff hb j k hjk).mpr hw₂)
      by_cases hw₄ : l.w.force i r = 0
      · have hz₄ := he₄.resolve_right (not_not.mpr hw₄)
        have hs₄ := p₄.single_z_separations ((l.pair_z_stroke_iff hb i r hir).mpr hz₄)
          ((l.pair_w_absent_iff hb i r hir).mpr hw₄)
        have hsmall : p₃.w =o[atTop] p₃.eps :=
          ((hs₄.2.sub hs₁.2).sub hs₂.2).congr_left (fun t => by
            change ((q t).w i - (q t).w r) - ((q t).w i - (q t).w j) -
              ((q t).w j - (q t).w k) = (q t).w k - (q t).w r
            ring)
        exact hsmall.not_isBigO (Eventually.of_forall p₃.w_ne_zero).frequently
          (p₃.swap.stroke_z_lower hf₃)
      · have hf₄ := (l.pair_w_stroke_iff hb i r hir).mpr hw₄
        let p := ZWSystem.pairEstimateData q hb i k hik
        apply p.not_mixed_small
        · exact ((p₄.swap.stroke_w_upper hf₄).sub (p₃.swap.stroke_w_upper hf₃)).congr_left
            (fun t => by
              change ((q t).z i - (q t).z r) - ((q t).z k - (q t).z r) =
                (q t).z i - (q t).z k
              ring)
        · exact (hs₁.2.add hs₂.2).congr_left (fun t => by
            change ((q t).w i - (q t).w j) + ((q t).w j - (q t).w k) =
              (q t).w i - (q t).w k
            ring)
    · have hf₂ := (l.pair_w_stroke_iff hb j k hjk).mpr hw₂
      by_cases hw₄ : l.w.force i r = 0
      · have hz₄ := he₄.resolve_right (not_not.mpr hw₄)
        have hs₄ := p₄.single_z_separations ((l.pair_z_stroke_iff hb i r hir).mpr hz₄)
          ((l.pair_w_absent_iff hb i r hir).mpr hw₄)
        let p := ZWSystem.pairEstimateData q hb j r hjr
        apply p.not_mixed_small
        · exact ((p₂.swap.stroke_w_upper hf₂).add (p₃.swap.stroke_w_upper hf₃)).congr_left
            (fun t => by
              change ((q t).z j - (q t).z k) + ((q t).z k - (q t).z r) =
                (q t).z j - (q t).z r
              ring)
        · exact (hs₄.2.sub hs₁.2).congr_left (fun t => by
            change ((q t).w i - (q t).w r) - ((q t).w i - (q t).w j) =
              (q t).w j - (q t).w r
            ring)
      · have hf₄ := (l.pair_w_stroke_iff hb i r hir).mpr hw₄
        have hbound : p₁.z =O[atTop] p₁.eps :=
          (((p₄.swap.stroke_w_upper hf₄).sub (p₃.swap.stroke_w_upper hf₃)).sub
            (p₂.swap.stroke_w_upper hf₂)).congr_left (fun t => by
              change ((q t).z i - (q t).z r) - ((q t).z k - (q t).z r) -
                ((q t).z j - (q t).z k) = (q t).z i - (q t).z j
              ring)
        exact hs₁.1.not_isBigO (Eventually.of_forall p₁.eps_ne_zero).frequently hbound
  exact ⟨he₃.resolve_right (not_not.mpr hw₃), hw₃⟩

theorem quadrilateral_w_only_opposite (i j k r : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hir : i ≠ r)
    (hjk : j ≠ k) (hjr : j ≠ r) (hkr : k ≠ r)
    (hw₁ : l.w.force i j ≠ 0) (hz₁ : l.z.force i j = 0)
    (he₂ : l.z.force j k ≠ 0 ∨ l.w.force j k ≠ 0)
    (he₃ : l.z.force k r ≠ 0 ∨ l.w.force k r ≠ 0)
    (he₄ : l.z.force i r ≠ 0 ∨ l.w.force i r ≠ 0) :
    l.w.force k r ≠ 0 ∧ l.z.force k r = 0 :=
  (l.swapBalanced hb).quadrilateral_z_only_opposite (fun t => (hb t).symm)
    i j k r hij hik hir hjk hjr hkr hw₁ hz₁ he₂.symm he₃.symm he₄.symm

/-- The full edge-type assertion of Rule 2g, for one pair of opposite sides. -/
theorem quadrilateral_opposite_types (i j k r : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hir : i ≠ r)
    (hjk : j ≠ k) (hjr : j ≠ r) (hkr : k ≠ r)
    (he₁ : l.z.force i j ≠ 0 ∨ l.w.force i j ≠ 0)
    (he₂ : l.z.force j k ≠ 0 ∨ l.w.force j k ≠ 0)
    (he₃ : l.z.force k r ≠ 0 ∨ l.w.force k r ≠ 0)
    (he₄ : l.z.force i r ≠ 0 ∨ l.w.force i r ≠ 0) :
    (l.z.force i j ≠ 0 ↔ l.z.force k r ≠ 0) ∧
      (l.w.force i j ≠ 0 ↔ l.w.force k r ≠ 0) := by
  by_cases hz₁ : l.z.force i j = 0
  · have hw₁ := he₁.resolve_left (not_not.mpr hz₁)
    have h := l.quadrilateral_w_only_opposite hb i j k r hij hik hir hjk hjr hkr
      hw₁ hz₁ he₂ he₃ he₄
    simp [hz₁, hw₁, h.1, h.2]
  · by_cases hw₁ : l.w.force i j = 0
    · have h := l.quadrilateral_z_only_opposite hb i j k r hij hik hir hjk hjr hkr
        hz₁ hw₁ he₂ he₃ he₄
      simp [hz₁, hw₁, h.1, h.2]
    · have hz₃ : l.z.force k r ≠ 0 := by
        intro hz₃
        have hw₃ := he₃.resolve_left (not_not.mpr hz₃)
        have h := l.quadrilateral_w_only_opposite hb k r i j hkr (Ne.symm hik) (Ne.symm hjk)
          (Ne.symm hir) (Ne.symm hjr) hij hw₃ hz₃ (l.edge_symm i r he₄) he₁ (l.edge_symm j k he₂)
        exact hz₁ h.2
      have hw₃ : l.w.force k r ≠ 0 := by
        intro hw₃
        have h := l.quadrilateral_z_only_opposite hb k r i j hkr (Ne.symm hik) (Ne.symm hjk)
          (Ne.symm hir) (Ne.symm hjr) hij hz₃ hw₃ (l.edge_symm i r he₄) he₁ (l.edge_symm j k he₂)
        exact hw₁ h.2
      simp [hz₁, hw₁, hz₃, hw₃]

theorem quadrilateral_opposite_entries (i j k r : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hir : i ≠ r)
    (hjk : j ≠ k) (hjr : j ≠ r) (hkr : k ≠ r)
    (he₁ : l.z.matrix i j + l.w.matrix i j ≠ 0)
    (he₂ : l.z.matrix j k + l.w.matrix j k ≠ 0)
    (he₃ : l.z.matrix k r + l.w.matrix k r ≠ 0)
    (he₄ : l.z.matrix i r + l.w.matrix i r ≠ 0) :
    l.z.matrix i j = l.z.matrix k r ∧ l.w.matrix i j = l.w.matrix k r := by
  have h := l.quadrilateral_opposite_types hb i j k r hij hik hir hjk hjr hkr
    ((l.matrix_edge_iff i j hij).mp he₁) ((l.matrix_edge_iff j k hjk).mp he₂)
    ((l.matrix_edge_iff k r hkr).mp he₃) ((l.matrix_edge_iff i r hir).mp he₄)
  constructor
  · simp only [OneColorLimit.matrix, OneColorLimit.Incident, if_neg hij, if_neg hkr, h.1]
  · simp only [OneColorLimit.matrix, OneColorLimit.Incident, if_neg hij, if_neg hkr, h.2]

end ScaledZWLimit

def SecondQuadrilateralRule {n : ℕ} (A B : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j k r, i ≠ j → i ≠ k → i ≠ r → j ≠ k → j ≠ r → k ≠ r →
    A i j + B i j ≠ 0 → A j k + B j k ≠ 0 →
    A k r + B k r ≠ 0 → A i r + B i r ≠ 0 →
    A i j + A k r ≠ 1 ∧ A j k + A i r ≠ 1 ∧
    B i j + B k r ≠ 1 ∧ B j k + B i r ≠ 1

structure QuadrilateralMatrixRules {n : ℕ} (A B : Fin n → Fin n → ℕ) : Prop where
  firstA : FirstQuadrilateralRule A
  firstB : FirstQuadrilateralRule B
  second : SecondQuadrilateralRule A B

theorem ScaledZWLimit.quadrilateralMatrixRules {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) :
    QuadrilateralMatrixRules l.z.matrix l.w.matrix := by
  refine ⟨l.first_quadrilateral_rule hb,
    (l.swapBalanced hb).first_quadrilateral_rule (fun t => (hb t).symm), ?_⟩
  intro i j k r hij hik hir hjk hjr hkr he₁ he₂ he₃ he₄
  have h₁ := l.quadrilateral_opposite_entries hb i j k r hij hik hir hjk hjr hkr he₁ he₂ he₃ he₄
  have h₂ := l.quadrilateral_opposite_entries hb j k r i hjk hjr (Ne.symm hij) hkr (Ne.symm hik)
    (Ne.symm hir) he₂ he₃
    (by simpa only [l.z.matrix_symm r i, l.w.matrix_symm r i] using he₄)
    (by simpa only [l.z.matrix_symm j i, l.w.matrix_symm j i] using he₁)
  rw [l.z.matrix_symm r i, l.w.matrix_symm r i] at h₂
  omega

end CentralConfigurations
