import CentralConfigurations.Asymptotics.AlgebraicUnbounded
import CentralConfigurations.Model.Invariance

/-!
# The exact potential-level affine ideal

The scalar of a physical normalized point is added as an equation, rather
than transported along an unformalized curve. No physical reality is asserted
for other points of this complex level. Balancing may leave the gauge.
-/

namespace CentralConfigurations
noncomputable section
open scoped BigOperators

namespace PolynomialEncoding

def fixedPotentialIdeal {n : ℕ} (mass : Fin n → ℂ) (i j : Fin n) (c : ℂ) :
    Ideal (MvPolynomial (Coordinate n) ℂ) :=
  gaugedIdeal mass i j ⊔ Ideal.span {potentialPolynomial mass - MvPolynomial.C c}

theorem mem_fixedPotential_zeroLocus_iff {n : ℕ} (mass : Fin n → ℂ)
    (i j : Fin n) (c : ℂ) (a : Coordinate n → ℂ) :
    a ∈ MvPolynomial.zeroLocus ℂ (fixedPotentialIdeal mass i j c) ↔
      ((∀ e, MvPolynomial.eval a (equations mass e) = 0) ∧
        a (yCoord i) = a (yCoord j)) ∧
      MvPolynomial.aeval a (potentialPolynomial mass) = c := by
  change (fixedPotentialIdeal mass i j c ≤ RingHom.ker (MvPolynomial.aeval a)) ↔ _
  rw [fixedPotentialIdeal, sup_le_iff]
  change (a ∈ MvPolynomial.zeroLocus ℂ (gaugedIdeal mass i j) ∧ _) ↔ _
  rw [mem_gauged_zeroLocus_iff]
  simp [Ideal.span_le, Set.singleton_subset_iff, RingHom.mem_ker, sub_eq_zero]

end PolynomialEncoding

def fixedPotentialGauge {n : ℕ} (mass : Fin n → ℂ) (i j : Fin n) (c : ℂ) :
    Set (NormalizedSystem ℂ n mass) :=
  {q | q.InGauge i j ∧ q.unorderedPotential = c}

theorem fixedPotential_assignment_mem {n : ℕ} {mass : Fin n → ℂ}
    {i j : Fin n} {c : ℂ} (q : NormalizedSystem ℂ n mass)
    (hq : q ∈ fixedPotentialGauge mass i j c) :
    PolynomialEncoding.assignment q ∈ MvPolynomial.zeroLocus ℂ
      (PolynomialEncoding.fixedPotentialIdeal mass i j c) := by
  apply (PolynomialEncoding.mem_fixedPotential_zeroLocus_iff mass i j c _).mpr
  exact ⟨⟨PolynomialEncoding.normalized_vanishes q, hq.1.2⟩,
    (PolynomialEncoding.eval_potentialPolynomial mass q).trans hq.2⟩

theorem fixedPotential_ofCommonZero_mem {n : ℕ} (mass : Fin n → ℂ)
    (i j : Fin n) (hij : i ≠ j) (c : ℂ) (a : PolynomialEncoding.Coordinate n → ℂ)
    (ha : a ∈ MvPolynomial.zeroLocus ℂ
      (PolynomialEncoding.fixedPotentialIdeal mass i j c)) :
    ∃ q : NormalizedSystem ℂ n mass, q ∈ fixedPotentialGauge mass i j c ∧
      PolynomialEncoding.assignment q = a := by
  obtain ⟨⟨he, hg⟩, hp⟩ :=
    (PolynomialEncoding.mem_fixedPotential_zeroLocus_iff mass i j c a).mp ha
  let q := PolynomialEncoding.ofCommonZero mass a he
  have hqa : PolynomialEncoding.assignment q = a :=
    PolynomialEncoding.assignment_ofCommonZero mass a he
  refine ⟨q, ⟨⟨hij, hg⟩, ?_⟩, hqa⟩
  rw [← PolynomialEncoding.eval_potentialPolynomial mass q, hqa]
  exact hp

theorem ZWSystem.rescale_unorderedPotential {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (a : ℂ) (ha : a ≠ 0) :
    (q.rescale a ha).toNormalized.unorderedPotential = q.toNormalized.unorderedPotential := rfl

theorem ZWSystem.swap_unorderedPotential {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) :
    q.swap.toNormalized.unorderedPotential = q.toNormalized.unorderedPotential := rfl

theorem ZWSystem.balanced_unorderedPotential {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) :
    (q.balanced i j hij).toNormalized.unorderedPotential = q.toNormalized.unorderedPotential := rfl

theorem NormalizedSystem.map_unorderedPotential {K L : Type*} [CommRing K] [CommRing L]
    {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass) (f : K →+* L) :
    (q.map f).unorderedPotential = f q.unorderedPotential := by
  simp [NormalizedSystem.unorderedPotential, NormalizedSystem.map, apply_ite]

theorem NormalizedSystem.relabel_unorderedPotential {K : Type*} [Field K] [CharZero K]
    {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass) (e : Fin n ≃ Fin n) :
    (q.relabel e).unorderedPotential = q.unorderedPotential := by
  rw [NormalizedSystem.unorderedPotential_eq_inertia,
    NormalizedSystem.unorderedPotential_eq_inertia]
  unfold NormalizedSystem.inertia NormalizedSystem.relabel
  exact e.sum_comp (fun i => mass i * (q.x i ^ 2 + q.y i ^ 2))

theorem NormalizedSystem.fixedPotential_subsequence {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → NormalizedSystem ℂ n mass} {c : ℂ}
    (h : ∀ t, (q t).unorderedPotential = c) (φ : ℕ → ℕ) :
    ∀ t, (q (φ t)).unorderedPotential = c := fun t => h (φ t)

theorem ZWSystem.fixedPotential_balanced_subsequence {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {c : ℂ}
    (h : ∀ t, (q t).toNormalized.unorderedPotential = c)
    (i j : Fin n) (hij : i ≠ j) (φ : ℕ → ℕ) :
    ∀ t, ((q (φ t)).balanced i j hij).toNormalized.potential = c := by
  intro t
  rw [NormalizedSystem.potential_eq_unordered, ZWSystem.balanced_unorderedPotential]
  exact h (φ t)

end
end CentralConfigurations
