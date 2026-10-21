import CentralConfigurations.FiveBody.SimpleMassRelations

namespace CentralConfigurations
noncomputable section
open Filter
open scoped Topology
namespace ScaledZWLimit
variable {mass : Fin 5 → ℝ}
  {q : ℕ → ZWSystem ℂ 5 (fun a => (mass a : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : ∀ a, 0 < mass a)
include hb hm

theorem five_body_source4_secondary_triangle_mass_polynomial
    (hd : l.diagramCode = fiveBodySourceDiagram 3) :
    kiteMassPolynomial (mass 2) (mass 3) (mass 4) = 0 :=
  l.secondary_triangle_w_pivot_mass_of_code hd hb hm 2 3 4
    (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem five_body_source4_secondary_triangle_radical_relation
    (hd : l.diagramCode = fiveBodySourceDiagram 3) :
    kiteRadicalSourceMassRelation (mass 2) (mass 3) (mass 4) = 0 :=
  kite_radical_source_relation_of_polynomial _ _ _ (hm 2) (hm 3) (hm 4)
    (l.five_body_source4_secondary_triangle_mass_polynomial hb hm hd)

theorem five_body_source7_secondary_triangle_mass_polynomial
    (hd : l.diagramCode = fiveBodySourceDiagram 6) :
    kiteMassPolynomial (mass 2) (mass 3) (mass 4) = 0 :=
  l.secondary_triangle_w_pivot_mass_of_code hd hb hm 2 3 4
    (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem five_body_source7_secondary_triangle_radical_relation
    (hd : l.diagramCode = fiveBodySourceDiagram 6) :
    kiteRadicalSourceMassRelation (mass 2) (mass 3) (mass 4) = 0 :=
  kite_radical_source_relation_of_polynomial _ _ _ (hm 2) (hm 3) (hm 4)
    (l.five_body_source7_secondary_triangle_mass_polynomial hb hm hd)

theorem five_body_source4_reverse_secondary_triangle_mass_polynomial
    (hd : l.diagramCode = fiveBodySourceDiagram 3) :
    kiteMassPolynomial (mass 0) (mass 1) (mass 4) = 0 := by
  have hs : (l.swapBalanced hb).diagramCode =
      ((fiveBodySourceDiagram 3).2,(fiveBodySourceDiagram 3).1) := by
    change (l.diagramCode.2,l.diagramCode.1) = _
    rw [hd]
  exact (l.swapBalanced hb).secondary_triangle_w_pivot_mass_of_code hs
    (fun t => (hb t).symm) hm 0 1 4
    (by decide) (by decide) (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem five_body_source4_both_secondary_mass_polynomials
    (hd : l.diagramCode = fiveBodySourceDiagram 3) :
    kiteMassPolynomial (mass 2) (mass 3) (mass 4) = 0 ∧
      kiteMassPolynomial (mass 0) (mass 1) (mass 4) = 0 :=
  ⟨l.five_body_source4_secondary_triangle_mass_polynomial hb hm hd,
    l.five_body_source4_reverse_secondary_triangle_mass_polynomial hb hm hd⟩

theorem five_body_source4_reverse_radical_relation
    (hd : l.diagramCode = fiveBodySourceDiagram 3) :
    kiteRadicalSourceMassRelation (mass 0) (mass 1) (mass 4) = 0 :=
  kite_radical_source_relation_of_polynomial _ _ _ (hm 0) (hm 1) (hm 4)
    (l.five_body_source4_reverse_secondary_triangle_mass_polynomial hb hm hd)

theorem five_body_source5_external_triangle_mass_cases
    (hd : l.diagramCode = fiveBodySourceDiagram 4) :
    kiteMassPolynomial (mass 2) (mass 3) (mass 4) = 0 ∨
    kiteMassPolynomial (mass 3) (mass 4) (mass 2) = 0 ∨
    kiteMassPolynomial (mass 4) (mass 2) (mass 3) = 0 :=
  l.secondary_triangle_external_w_star_mass_cases_of_code hd hb hm 2 3 4 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel)

theorem five_body_source5_source_lcm_relation
    (hd : l.diagramCode = fiveBodySourceDiagram 4) :
    MvPolynomial.eval (fun a => mass a ^ (1/4 : ℝ)) (sourceTriangleKiteLCM 2 3 4) = 0 :=
  source_triangle_kite_lcm_eval_zero mass hm 2 3 4
    (l.five_body_source5_external_triangle_mass_cases hb hm hd)

end ScaledZWLimit
end
end CentralConfigurations
