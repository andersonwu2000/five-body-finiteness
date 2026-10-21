import CentralConfigurations.FiveBody.SimpleMassRelations
import CentralConfigurations.Asymptotics.FourProductAlgebra
import Mathlib.Data.Fin.Tuple.Sort

/-! The complete labelled R-zero list, indexed by the complementary edge.
Repeated masses retain their distinct labels. -/

namespace CentralConfigurations.FiveBody.RZero
noncomputable section
open scoped BigOperators

def complementTriple : Fin 10 → Fin 3 → Fin 5 :=
  ![![2,3,4], ![1,3,4], ![1,2,4], ![1,2,3], ![0,3,4],
    ![0,2,4], ![0,2,3], ![0,1,4], ![0,1,3], ![0,1,2]]

def tripleLabels (e : Fin 10) : Finset (Fin 5) :=
  {complementTriple e 0, complementTriple e 1, complementTriple e 2}

theorem complementTriple_edge_indexing : ∀ e : Fin 10,
    fiveBodyEdges (fiveBodyDisjointEdges e 0) = (complementTriple e 0, complementTriple e 1) ∧
    fiveBodyEdges (fiveBodyDisjointEdges e 1) = (complementTriple e 0, complementTriple e 2) ∧
    fiveBodyEdges (fiveBodyDisjointEdges e 2) = (complementTriple e 1, complementTriple e 2) := by
  decide +kernel

theorem tripleLabels_card (e : Fin 10) : (tripleLabels e).card = 3 := by
  fin_cases e <;> decide +kernel

abbrev LabelledTriple := {s : Finset (Fin 5) // s.card = 3}

def tripleEquiv : Fin 10 ≃ LabelledTriple :=
  Equiv.ofBijective (fun e => ⟨tripleLabels e, tripleLabels_card e⟩)
    (by decide +kernel)

def trianglePolynomial (mass : Fin 5 → ℝ) (e : Fin 10) : ℝ :=
  triangleMassPolynomial (mass (complementTriple e 0))
    (mass (complementTriple e 1)) (mass (complementTriple e 2))

def completeR (mass : Fin 5 → ℝ) : Finset (Fin 10) :=
  Finset.univ.filter (fun e => trianglePolynomial mass e = 0)

@[simp] theorem mem_completeR (mass : Fin 5 → ℝ) (e : Fin 10) :
    e ∈ completeR mass ↔ trianglePolynomial mass e = 0 := by
  simp [completeR]

def reciprocalRoot (mass : Fin 5 → ℝ) (i : Fin 5) : ℝ := (Real.sqrt (mass i))⁻¹

def IsAdditiveTriple (x : Fin 5 → ℝ) (s : Finset (Fin 5)) : Prop :=
  ∃ i j k, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧ s = {i,j,k} ∧ x k = x i + x j

def additiveTriples (x : Fin 5 → ℝ) : Finset LabelledTriple :=
  by classical exact Finset.univ.filter (fun s => IsAdditiveTriple x s.val)

@[simp] theorem mem_additiveTriples (x : Fin 5 → ℝ) (s : LabelledTriple) :
    s ∈ additiveTriples x ↔ IsAdditiveTriple x s.val := by
  simp [additiveTriples]

theorem polynomial_zero_of_reciprocal_add (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : (Real.sqrt a)⁻¹ = (Real.sqrt b)⁻¹ + (Real.sqrt c)⁻¹) :
    triangleMassPolynomial a b c = 0 := by
  have hsa : Real.sqrt a ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hsb : Real.sqrt b ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hb)
  have hsc : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hc)
  have hm : triangleMu1 a b c = 0 := by
    field_simp [hsa, hsb, hsc] at h
    dsimp [triangleMu1]
    nlinarith [h]
  rw [triangle_mass_polynomial_factorization a b c ha.le hb.le hc.le]
  simp [triangleMu3, hm]

theorem polynomial_zero_iff_reciprocal_cases (a b c : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    triangleMassPolynomial a b c = 0 ↔
      (Real.sqrt a)⁻¹ = (Real.sqrt b)⁻¹ + (Real.sqrt c)⁻¹ ∨
      (Real.sqrt b)⁻¹ = (Real.sqrt c)⁻¹ + (Real.sqrt a)⁻¹ ∨
      (Real.sqrt c)⁻¹ = (Real.sqrt a)⁻¹ + (Real.sqrt b)⁻¹ := by
  constructor
  · exact triangle_reciprocal_cases_of_polynomial a b c ha hb hc
  · rintro (h | h | h)
    · exact polynomial_zero_of_reciprocal_add a b c ha hb hc h
    · have hz := polynomial_zero_of_reciprocal_add b c a hb hc ha h
      dsimp [triangleMassPolynomial] at hz ⊢
      linear_combination hz
    · have hz := polynomial_zero_of_reciprocal_add c a b hc ha hb h
      dsimp [triangleMassPolynomial] at hz ⊢
      linear_combination hz

theorem additive_on_triple_iff (x : Fin 5 → ℝ) (e : Fin 10) :
    IsAdditiveTriple x (tripleLabels e) ↔
      x (complementTriple e 0) = x (complementTriple e 1) + x (complementTriple e 2) ∨
      x (complementTriple e 1) = x (complementTriple e 2) + x (complementTriple e 0) ∨
      x (complementTriple e 2) = x (complementTriple e 0) + x (complementTriple e 1) := by
  constructor
  · rintro ⟨i,j,k,hij,hik,hjk,hs,hx⟩
    have hi : i ∈ tripleLabels e := by rw [hs]; simp
    have hj : j ∈ tripleLabels e := by rw [hs]; simp
    have hk : k ∈ tripleLabels e := by rw [hs]; simp
    simp only [tripleLabels, Finset.mem_insert, Finset.mem_singleton] at hi hj hk
    rcases hi with rfl | rfl | rfl <;>
      rcases hj with rfl | rfl | rfl <;>
      rcases hk with rfl | rfl | rfl <;>
      first | exact (hij rfl).elim | exact (hik rfl).elim | exact (hjk rfl).elim |
        simp_all [add_comm]
  · rintro (h | h | h)
    · refine ⟨complementTriple e 1, complementTriple e 2, complementTriple e 0,
        ?_, ?_, ?_, ?_, h⟩
      all_goals fin_cases e <;> decide +kernel
    · refine ⟨complementTriple e 2, complementTriple e 0, complementTriple e 1,
        ?_, ?_, ?_, ?_, h⟩
      all_goals fin_cases e <;> decide +kernel
    · refine ⟨complementTriple e 0, complementTriple e 1, complementTriple e 2,
        ?_, ?_, ?_, rfl, h⟩
      all_goals fin_cases e <;> decide +kernel

theorem mem_completeR_iff_additive (mass : Fin 5 → ℝ) (hm : ∀ i, 0 < mass i)
    (e : Fin 10) :
    e ∈ completeR mass ↔ IsAdditiveTriple (reciprocalRoot mass) (tripleLabels e) := by
  rw [mem_completeR, trianglePolynomial, additive_on_triple_iff]
  exact polynomial_zero_iff_reciprocal_cases _ _ _ (hm _) (hm _) (hm _)

theorem completeR_card_eq_additive (mass : Fin 5 → ℝ) (hm : ∀ i, 0 < mass i) :
    (completeR mass).card = (additiveTriples (reciprocalRoot mass)).card := by
  apply Finset.card_bij (fun e _ => tripleEquiv e)
  · intro e he
    exact (mem_additiveTriples _ _).mpr ((mem_completeR_iff_additive mass hm e).mp he)
  · intro a ha b hb hab
    exact tripleEquiv.injective hab
  · intro s hs
    refine ⟨tripleEquiv.symm s, ?_, tripleEquiv.apply_symm_apply s⟩
    apply (mem_completeR_iff_additive mass hm _).mpr
    have he := congrArg Subtype.val (tripleEquiv.apply_symm_apply s)
    change tripleLabels (tripleEquiv.symm s) = s.val at he
    rw [he]
    exact (mem_additiveTriples _ _).mp hs

theorem d5_internal_mem_completeR (mass : Fin 5 → ℝ) (hm : ∀ i, 0 < mass i)
    {q : ℕ → ZWSystem ℂ 5 (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hd : l.diagramCode = fiveBodySourceDiagram 2) :
    (0 : Fin 10) ∈ completeR mass := by
  rw [mem_completeR]
  exact l.five_body_source3_triangle_mass_polynomial hm hd

end
end CentralConfigurations.FiveBody.RZero
