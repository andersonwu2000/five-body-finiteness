import CentralConfigurations.FiveBody.D2Resonance.SignClasses
import CentralConfigurations.FiveBody.D2Resonance.PositiveClassification

noncomputable section
open Polynomial
namespace CentralConfigurations.FiveBody.D2.Resonance
open Exceptional
set_option maxHeartbeats 2000000

def CompleteRepeatedCases (a b c : ℝ) (x s13 s23 : ℂ) : Prop :=
  (s13=1 ∧ s23=1 ∧ PositiveRepeatedCase a b c x) ∨
  (s13=1 ∧ s23=-1 ∧ PositiveRepeatedCase a c b (1/x)) ∨
  (s13=-1 ∧ s23=-1 ∧ PositiveRepeatedCase b a c (1-x))

theorem repeatedGap_complete_cases {a b c : ℝ} {x s13 s23 : ℂ}
    (h : RepeatedGap a b c x s13 s23) (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (h13 : s13=1 ∨ s13=-1) (h23 : s23=1 ∨ s23=-1) :
    CompleteRepeatedCases a b c x s13 s23 := by
  rcases h13 with rfl | rfl <;> rcases h23 with rfl | rfl
  · obtain ⟨h0,h1⟩ := h.polynomial_zeros
    exact Or.inl ⟨rfl,rfl,positive_repeated_classification a b c x ha hb hc h0 h1⟩
  · obtain ⟨h0,h1⟩ := h.swap12.polynomial_zeros
    exact Or.inr (Or.inl ⟨rfl,rfl,positive_repeated_classification a c b (1/x) ha hc hb h0 h1⟩)
  · exact False.elim (h.alternating_false ha hb hc)
  · obtain ⟨h0,h1⟩ := h.swap01.polynomial_zeros
    exact Or.inr (Or.inr ⟨rfl,rfl,positive_repeated_classification b a c (1-x) hb ha hc h0 h1⟩)

theorem GapData.repeatedGap {n : Fin 3 → ℝ}
    {r : ZWSystem ℂ 3 (fun i => (n i:ℂ))} (d : GapData r)
    (hell : transverseEigenvalue r=-(1/2:ℂ)) :
    RepeatedGap (n 0) (n 1) (n 2) d.x d.sign13 d.sign23 := by
  have ht := d.trace
  change transverseEigenvalue r =
    gapTrace (n 0:ℂ) (n 1:ℂ) (n 2:ℂ) d.x d.sign13 d.sign23/d.lam-1 at ht
  rw [hell] at ht
  field_simp [d.lam_ne_zero] at ht
  refine ⟨d.x_ne_zero,d.x_ne_one,d.euler_zero,?_⟩
  rw [← d.original_rows.1]
  linear_combination ht

theorem GapData.complete_resonance_cases {n : Fin 3 → ℝ}
    {r : ZWSystem ℂ 3 (fun i => (n i:ℂ))} (d : GapData r)
    (hn : ∀i, 0<n i) (hell : transverseEigenvalue r=-(1/2:ℂ)) :
    CompleteRepeatedCases (n 0) (n 1) (n 2) d.x d.sign13 d.sign23 :=
  repeatedGap_complete_cases (GapData.repeatedGap d hell) (hn 0) (hn 1) (hn 2)
    d.sign13_values d.sign23_values

theorem actual_complete_resonance_cases {n : Fin 3 → ℝ}
    {r : ZWSystem ℂ 3 (fun i => (n i:ℂ))} (s : SignedEulerMetric r)
    (hn : ∀i, 0<n i) (hell : transverseEigenvalue r=-(1/2:ℂ)) :
    ∃ d : GapData r,
      CompleteRepeatedCases (n 0) (n 1) (n 2) d.x d.sign13 d.sign23 := by
  obtain ⟨d⟩ := exists_gapData s
  exact ⟨d,GapData.complete_resonance_cases d hn hell⟩

end CentralConfigurations.FiveBody.D2.Resonance
