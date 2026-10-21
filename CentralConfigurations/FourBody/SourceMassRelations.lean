import CentralConfigurations.Enumeration.FourBodyFigures
import CentralConfigurations.Diagrams.ThreeRowTriangleMass
import CentralConfigurations.Diagrams.TwoRowKiteMass
import CentralConfigurations.Algebra.KiteRadicalSource

/-!
# Actual mass restrictions of Sections 9.2, 9.3 and 9.5

The code list is in the original Figure 8 order. Each argument starts from
an actual singular limit, checks the concrete four-body incidence pattern,
and invokes proved force, ratio and elimination lemmas. In particular the
Section 9.3 conclusion includes its literal eleven-factor radical product.
Section 9.4's actual disconnected wedge argument is connected separately
in `FourBody/DisconnectedPair.lean`.
-/

namespace CentralConfigurations
noncomputable section
open scoped Topology
open Filter

def fourBodySourceDiagram (k : Fin 5) : DiagramCode 4 :=
  let p : ℕ × ℕ := ![(366, 366), (352, 352), (352, 1017), (896, 19), (915, 697)] k
  (BinaryMatrixCode.fromMask 4 p.1, BinaryMatrixCode.fromMask 4 p.2)

theorem four_body_source_diagram_image :
    Finset.univ.image fourBodySourceDiagram = fourBodySourceRepresentatives := by decide +kernel

theorem four_body_source_diagram_injective : Function.Injective fourBodySourceDiagram := by
  decide +kernel

theorem triangle_reciprocal_relation_of_mu1 (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : triangleMu1 a b c = 0) :
    (Real.sqrt a)⁻¹ = (Real.sqrt b)⁻¹ + (Real.sqrt c)⁻¹ := by
  have hA := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hB := ne_of_gt (Real.sqrt_pos.mpr hb)
  have hC := ne_of_gt (Real.sqrt_pos.mpr hc)
  dsimp [triangleMu1] at h
  field_simp [hA, hB, hC]
  linear_combination -h

theorem ScaledZWLimit.four_body_source2_mass_polynomial {mass : Fin 4 → ℝ}
    {q : ℕ → ZWSystem ℂ 4 (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ a, 0 < mass a)
    (hd : l.diagramCode = fourBodySourceDiagram 1) :
    triangleMassPolynomial (mass 1) (mass 2) (mass 3) = 0 :=
  l.three_uncircled_triangle_rows_of_code hd hm 1 2 3
    (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- Equation (9.2), with all three possible distinguished masses retained. -/
theorem ScaledZWLimit.four_body_source2_reciprocal_mass_relation {mass : Fin 4 → ℝ}
    {q : ℕ → ZWSystem ℂ 4 (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ a, 0 < mass a)
    (hd : l.diagramCode = fourBodySourceDiagram 1) :
    (Real.sqrt (mass 1))⁻¹ = (Real.sqrt (mass 2))⁻¹ + (Real.sqrt (mass 3))⁻¹ ∨
    (Real.sqrt (mass 2))⁻¹ = (Real.sqrt (mass 3))⁻¹ + (Real.sqrt (mass 1))⁻¹ ∨
    (Real.sqrt (mass 3))⁻¹ = (Real.sqrt (mass 1))⁻¹ + (Real.sqrt (mass 2))⁻¹ := by
  have h := triangle_mu3_eq_zero_of_polynomial _ _ _ (hm 1) (hm 2) (hm 3)
    (l.four_body_source2_mass_polynomial hm hd)
  simp only [triangleMu3, mul_eq_zero] at h
  rcases h with (h | h) | h
  · exact Or.inl (triangle_reciprocal_relation_of_mu1 _ _ _ (hm 1) (hm 2) (hm 3) h)
  · exact Or.inr (Or.inl (triangle_reciprocal_relation_of_mu1 _ _ _ (hm 2) (hm 3) (hm 1) h))
  · exact Or.inr (Or.inr (triangle_reciprocal_relation_of_mu1 _ _ _ (hm 3) (hm 1) (hm 2) h))

theorem ScaledZWLimit.four_body_source2_printed_six_factors {mass : Fin 4 → ℝ}
    {q : ℕ → ZWSystem ℂ 4 (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ a, 0 < mass a)
    (hd : l.diagramCode = fourBodySourceDiagram 1) :
    trianglePrintedSixFactors (mass 1) (mass 2) (mass 3) = 0 := by
  rw [triangle_printed_six_factors_eq,
    triangle_mu5_eq_zero_of_polynomial _ _ _ (hm 1) (hm 2) (hm 3)
      (l.four_body_source2_mass_polynomial hm hd), neg_zero]

theorem ScaledZWLimit.four_body_source3_mass_polynomial {mass : Fin 4 → ℝ}
    {q : ℕ → ZWSystem ℂ 4 (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ a, 0 < mass a)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hd : l.diagramCode = fourBodySourceDiagram 2) :
    kiteMassPolynomial (mass 1) (mass 2) (mass 3) = 0 :=
  l.two_kite_rows_of_code hd ha hm 1 2 3
    (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

/-- The eleven-factor source expression of Section 9.3, with its radical factor. -/
theorem ScaledZWLimit.four_body_source3_radical_source_relation {mass : Fin 4 → ℝ}
    {q : ℕ → ZWSystem ℂ 4 (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ a, 0 < mass a)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hd : l.diagramCode = fourBodySourceDiagram 2) :
    kiteRadicalSourceMassRelation (mass 1) (mass 2) (mass 3) = 0 :=
  kite_radical_source_relation_of_polynomial _ _ _ (hm 1) (hm 2) (hm 3)
    (l.four_body_source3_mass_polynomial hm ha hd)

/-- The square-diagram mass identity (9.5). -/
theorem ScaledZWLimit.four_body_source5_mass_relation {mass : Fin 4 → ℂ}
    {q : ℕ → ZWSystem ℂ 4 mass}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hd : l.diagramCode = fourBodySourceDiagram 4) :
    mass 0 * mass 2 = mass 1 * mass 3 := by
  have h1 : l.w.position 1 = l.w.position 0 :=
    l.w_position_eq_of_z_code_edge hd ha 1 0 (by decide) (by decide +kernel)
  have h3 : l.w.position 3 = l.w.position 2 :=
    l.w_position_eq_of_z_code_edge hd ha 3 2 (by decide) (by decide +kernel)
  have hA := l.w_component_balance_of_code hd ({0, 3} : Finset (Fin 4)) (by decide +kernel)
  have hB := l.w_component_balance_of_code hd ({1, 2} : Finset (Fin 4)) (by decide +kernel)
  simp [h1, h3] at hA hB
  have hp := l.w_position_ne_zero_of_code hd 0 (by decide +kernel)
  have he : (mass 0 * mass 2 - mass 1 * mass 3) * l.w.position 0 = 0 := by
    linear_combination (mass 2) * hA - (mass 3) * hB
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hp)

end
end CentralConfigurations
