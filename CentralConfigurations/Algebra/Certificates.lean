import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial consequence certificates

Soundness interface for the computations of Chang (2023), Section 8.
An external computer algebra system may produce candidate multipliers;
their ideal-membership identities are proved in Lean.
-/

namespace CentralConfigurations

open scoped BigOperators

namespace Certificate

variable {R σ ι : Type*} [CommRing R] [Fintype ι]

/-- A polynomial consequence with an explicit ideal-membership identity. -/
structure IdealCombination (f : ι → MvPolynomial σ R) (p : MvPolynomial σ R) where
  multiplier : ι → MvPolynomial σ R
  identity : p = ∑ i, multiplier i * f i

/-- An ideal-combination certificate transports vanishing to its conclusion. -/
theorem IdealCombination.sound {f : ι → MvPolynomial σ R}
    {p : MvPolynomial σ R} (c : IdealCombination f p) (x : σ → R)
    (hf : ∀ i, MvPolynomial.eval x (f i) = 0) :
    MvPolynomial.eval x p = 0 := by
  rw [c.identity]
  simp [hf]

/-- A saturation/radical certificate, with the cancelled factor explicit. -/
structure SaturatedCombination (f : ι → MvPolynomial σ R)
    (denominator conclusion : MvPolynomial σ R) where
  denominatorPower : ℕ
  conclusionPower : ℕ
  combination : IdealCombination f
    (denominator ^ denominatorPower * conclusion ^ (conclusionPower + 1))

/-- Cancelling a supplied nonzero denominator is sound in a domain. -/
theorem SaturatedCombination.sound [IsDomain R]
    {f : ι → MvPolynomial σ R} {denominator conclusion : MvPolynomial σ R}
    (c : SaturatedCombination f denominator conclusion) (x : σ → R)
    (hf : ∀ i, MvPolynomial.eval x (f i) = 0)
    (hd : MvPolynomial.eval x denominator ≠ 0) :
    MvPolynomial.eval x conclusion = 0 := by
  have h := c.combination.sound x hf
  simp only [map_mul, map_pow] at h
  have hp : MvPolynomial.eval x conclusion ^ (c.conclusionPower + 1) = 0 :=
    (mul_eq_zero.mp h).resolve_left (pow_ne_zero _ hd)
  by_contra hn
  exact pow_ne_zero _ hn hp

/-- A common multiple of the branch relations vanishes if some covered branch does. -/
theorem branch_product_vanishes [DecidableEq ι]
    (p : ι → MvPolynomial σ R) (x : σ → R)
    (h : ∃ i, MvPolynomial.eval x (p i) = 0) :
    MvPolynomial.eval x (∏ i, p i) = 0 := by
  obtain ⟨i, hi⟩ := h
  simp only [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) hi

end Certificate
end CentralConfigurations
