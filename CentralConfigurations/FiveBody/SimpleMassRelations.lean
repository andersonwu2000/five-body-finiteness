import CentralConfigurations.Enumeration.FiveBodySourceData
import CentralConfigurations.FourBody.SourceMassRelations
import CentralConfigurations.Diagrams.SecondaryTriangleMass
import CentralConfigurations.Diagrams.ExternalTriangleCluster
import CentralConfigurations.Algebra.KiteSourceLCM

/-! Actual five-body mass restrictions on the original Figure 9 labels.
Every finite incidence hypothesis is kernel-checked. No source order table
or elimination program output is assumed. -/

namespace CentralConfigurations
noncomputable section
open Filter
open scoped Topology

theorem triangle_reciprocal_cases_of_polynomial (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : triangleMassPolynomial a b c = 0) :
    (Real.sqrt a)⁻¹ = (Real.sqrt b)⁻¹ + (Real.sqrt c)⁻¹ ∨
    (Real.sqrt b)⁻¹ = (Real.sqrt c)⁻¹ + (Real.sqrt a)⁻¹ ∨
    (Real.sqrt c)⁻¹ = (Real.sqrt a)⁻¹ + (Real.sqrt b)⁻¹ := by
  have hr := triangle_mu3_eq_zero_of_polynomial a b c ha hb hc h
  simp only [triangleMu3,mul_eq_zero] at hr
  rcases hr with (h | h) | h
  · exact Or.inl (triangle_reciprocal_relation_of_mu1 a b c ha hb hc h)
  · exact Or.inr (Or.inl (triangle_reciprocal_relation_of_mu1 b c a hb hc ha h))
  · exact Or.inr (Or.inr (triangle_reciprocal_relation_of_mu1 c a b hc ha hb h))

namespace ScaledZWLimit
variable {mass : Fin 5 → ℝ}
  {q : ℕ → ZWSystem ℂ 5 (fun a => (mass a : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ a, 0 < mass a)
include hm

theorem five_body_source1_triangle_mass_polynomial
    (hd : l.diagramCode = fiveBodySourceDiagram 0) :
    triangleMassPolynomial (mass 2) (mass 3) (mass 4) = 0 :=
  l.two_uncircled_triangle_rows_of_code hd hm 2 3 4
    (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem five_body_source1_printed_six_factors
    (hd : l.diagramCode = fiveBodySourceDiagram 0) :
    trianglePrintedSixFactors (mass 2) (mass 3) (mass 4) = 0 := by
  rw [triangle_printed_six_factors_eq,
    triangle_mu5_eq_zero_of_polynomial _ _ _ (hm 2) (hm 3) (hm 4)
      (l.five_body_source1_triangle_mass_polynomial hm hd),neg_zero]

theorem five_body_source1_reciprocal_mass_cases
    (hd : l.diagramCode = fiveBodySourceDiagram 0) :
    (Real.sqrt (mass 2))⁻¹ = (Real.sqrt (mass 3))⁻¹ + (Real.sqrt (mass 4))⁻¹ ∨
    (Real.sqrt (mass 3))⁻¹ = (Real.sqrt (mass 4))⁻¹ + (Real.sqrt (mass 2))⁻¹ ∨
    (Real.sqrt (mass 4))⁻¹ = (Real.sqrt (mass 2))⁻¹ + (Real.sqrt (mass 3))⁻¹ :=
  triangle_reciprocal_cases_of_polynomial _ _ _ (hm 2) (hm 3) (hm 4)
    (l.five_body_source1_triangle_mass_polynomial hm hd)

theorem five_body_source1_extra_factor_relation
    (hd : l.diagramCode = fiveBodySourceDiagram 0) :
    (mass 2 ^ (1/4 : ℝ) - mass 4 ^ (1/4 : ℝ)) *
      trianglePrintedSixFactors (mass 2) (mass 3) (mass 4) = 0 := by
  rw [l.five_body_source1_printed_six_factors hm hd,mul_zero]

theorem five_body_source3_triangle_mass_polynomial
    (hd : l.diagramCode = fiveBodySourceDiagram 2) :
    triangleMassPolynomial (mass 2) (mass 3) (mass 4) = 0 :=
  l.two_uncircled_triangle_rows_of_code hd hm 2 3 4
    (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem five_body_source3_printed_six_factors
    (hd : l.diagramCode = fiveBodySourceDiagram 2) :
    trianglePrintedSixFactors (mass 2) (mass 3) (mass 4) = 0 := by
  rw [triangle_printed_six_factors_eq,
    triangle_mu5_eq_zero_of_polynomial _ _ _ (hm 2) (hm 3) (hm 4)
      (l.five_body_source3_triangle_mass_polynomial hm hd),neg_zero]

theorem five_body_source3_reciprocal_mass_cases
    (hd : l.diagramCode = fiveBodySourceDiagram 2) :
    (Real.sqrt (mass 2))⁻¹ = (Real.sqrt (mass 3))⁻¹ + (Real.sqrt (mass 4))⁻¹ ∨
    (Real.sqrt (mass 3))⁻¹ = (Real.sqrt (mass 4))⁻¹ + (Real.sqrt (mass 2))⁻¹ ∨
    (Real.sqrt (mass 4))⁻¹ = (Real.sqrt (mass 2))⁻¹ + (Real.sqrt (mass 3))⁻¹ :=
  triangle_reciprocal_cases_of_polynomial _ _ _ (hm 2) (hm 3) (hm 4)
    (l.five_body_source3_triangle_mass_polynomial hm hd)

theorem five_body_source3_extra_factor_relation
    (hd : l.diagramCode = fiveBodySourceDiagram 2) :
    (mass 2 ^ (1/4 : ℝ) - mass 4 ^ (1/4 : ℝ)) *
      trianglePrintedSixFactors (mass 2) (mass 3) (mass 4) = 0 := by
  rw [l.five_body_source3_printed_six_factors hm hd,mul_zero]

theorem five_body_source6_triangle_mass_polynomial
    (hd : l.diagramCode = fiveBodySourceDiagram 5) :
    triangleMassPolynomial (mass 2) (mass 3) (mass 4) = 0 :=
  l.two_uncircled_triangle_rows_of_code hd hm 2 3 4
    (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem five_body_source6_printed_six_factors
    (hd : l.diagramCode = fiveBodySourceDiagram 5) :
    trianglePrintedSixFactors (mass 2) (mass 3) (mass 4) = 0 := by
  rw [triangle_printed_six_factors_eq,
    triangle_mu5_eq_zero_of_polynomial _ _ _ (hm 2) (hm 3) (hm 4)
      (l.five_body_source6_triangle_mass_polynomial hm hd),neg_zero]

theorem five_body_source6_reciprocal_mass_cases
    (hd : l.diagramCode = fiveBodySourceDiagram 5) :
    (Real.sqrt (mass 2))⁻¹ = (Real.sqrt (mass 3))⁻¹ + (Real.sqrt (mass 4))⁻¹ ∨
    (Real.sqrt (mass 3))⁻¹ = (Real.sqrt (mass 4))⁻¹ + (Real.sqrt (mass 2))⁻¹ ∨
    (Real.sqrt (mass 4))⁻¹ = (Real.sqrt (mass 2))⁻¹ + (Real.sqrt (mass 3))⁻¹ :=
  triangle_reciprocal_cases_of_polynomial _ _ _ (hm 2) (hm 3) (hm 4)
    (l.five_body_source6_triangle_mass_polynomial hm hd)

theorem five_body_source6_extra_factor_relation
    (hd : l.diagramCode = fiveBodySourceDiagram 5) :
    (mass 2 ^ (1/4 : ℝ) - mass 4 ^ (1/4 : ℝ)) *
      trianglePrintedSixFactors (mass 2) (mass 3) (mass 4) = 0 := by
  rw [l.five_body_source6_printed_six_factors hm hd,mul_zero]

theorem five_body_source8_triangle_mass_polynomial
    (hd : l.diagramCode = fiveBodySourceDiagram 7) :
    triangleMassPolynomial (mass 2) (mass 3) (mass 4) = 0 :=
  l.two_uncircled_triangle_rows_of_code hd hm 2 3 4
    (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem five_body_source8_printed_six_factors
    (hd : l.diagramCode = fiveBodySourceDiagram 7) :
    trianglePrintedSixFactors (mass 2) (mass 3) (mass 4) = 0 := by
  rw [triangle_printed_six_factors_eq,
    triangle_mu5_eq_zero_of_polynomial _ _ _ (hm 2) (hm 3) (hm 4)
      (l.five_body_source8_triangle_mass_polynomial hm hd),neg_zero]

theorem five_body_source8_reciprocal_mass_cases
    (hd : l.diagramCode = fiveBodySourceDiagram 7) :
    (Real.sqrt (mass 2))⁻¹ = (Real.sqrt (mass 3))⁻¹ + (Real.sqrt (mass 4))⁻¹ ∨
    (Real.sqrt (mass 3))⁻¹ = (Real.sqrt (mass 4))⁻¹ + (Real.sqrt (mass 2))⁻¹ ∨
    (Real.sqrt (mass 4))⁻¹ = (Real.sqrt (mass 2))⁻¹ + (Real.sqrt (mass 3))⁻¹ :=
  triangle_reciprocal_cases_of_polynomial _ _ _ (hm 2) (hm 3) (hm 4)
    (l.five_body_source8_triangle_mass_polynomial hm hd)

theorem five_body_source8_extra_factor_relation
    (hd : l.diagramCode = fiveBodySourceDiagram 7) :
    (mass 2 ^ (1/4 : ℝ) - mass 4 ^ (1/4 : ℝ)) *
      trianglePrintedSixFactors (mass 2) (mass 3) (mass 4) = 0 := by
  rw [l.five_body_source8_printed_six_factors hm hd,mul_zero]

theorem five_body_source10_kite_mass_polynomial
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hd : l.diagramCode = fiveBodySourceDiagram 9) :
    kiteMassPolynomial (mass 2) (mass 3) (mass 4) = 0 :=
  l.two_kite_rows_of_code hd ha hm 2 3 4
    (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem five_body_source10_kite_radical_relation
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hd : l.diagramCode = fiveBodySourceDiagram 9) :
    kiteRadicalSourceMassRelation (mass 2) (mass 3) (mass 4) = 0 :=
  kite_radical_source_relation_of_polynomial _ _ _ (hm 2) (hm 3) (hm 4)
    (l.five_body_source10_kite_mass_polynomial hm ha hd)

theorem five_body_source14_kite_mass_polynomial
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hd : l.diagramCode = fiveBodySourceDiagram 13) :
    kiteMassPolynomial (mass 2) (mass 3) (mass 4) = 0 :=
  l.two_kite_rows_of_code hd ha hm 2 3 4
    (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem five_body_source14_kite_radical_relation
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hd : l.diagramCode = fiveBodySourceDiagram 13) :
    kiteRadicalSourceMassRelation (mass 2) (mass 3) (mass 4) = 0 :=
  kite_radical_source_relation_of_polynomial _ _ _ (hm 2) (hm 3) (hm 4)
    (l.five_body_source14_kite_mass_polynomial hm ha hd)

end ScaledZWLimit

theorem ScaledZWLimit.five_body_source20_mass_relation {mass : Fin 5 → ℂ}
    {q : ℕ → ZWSystem ℂ 5 mass}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hd : l.diagramCode = fiveBodySourceDiagram 19) :
    mass 1 * mass 3 = mass 2 * mass 4 := by
  have h2 : l.w.position 2 = l.w.position 1 :=
    l.w_position_eq_of_z_code_edge hd ha 2 1 (by decide) (by decide +kernel)
  have h4 : l.w.position 4 = l.w.position 3 :=
    l.w_position_eq_of_z_code_edge hd ha 4 3 (by decide) (by decide +kernel)
  have hA := l.w_component_balance_of_code hd ({1,4} : Finset (Fin 5)) (by decide +kernel)
  have hB := l.w_component_balance_of_code hd ({2,3} : Finset (Fin 5)) (by decide +kernel)
  simp [h2,h4] at hA hB
  have hp := l.w_position_ne_zero_of_code hd 1 (by decide +kernel)
  have he : (mass 1 * mass 3 - mass 2 * mass 4) * l.w.position 1 = 0 := by
    linear_combination (mass 3)*hA-(mass 4)*hB
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hp)

end
end CentralConfigurations
