import CentralConfigurations.Algebra.FiniteValues
import CentralConfigurations.Model.PolynomialEncoding
import CentralConfigurations.Model.PotentialDifferential
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Lemma 2.2: finitely many potential values

The normalized equations are interpreted at the generic point of each
minimal prime of their ideal. Stationarity makes the potential constant
there; finiteness of minimal primes then gives finiteness of its values
on all normalized configurations. Masses remain fixed throughout.
-/

namespace CentralConfigurations

noncomputable section

open scoped BigOperators

namespace PolynomialEncoding

open MvPolynomial

variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L] {n : ℕ}

/-- Interpret the equations over an extension algebra, including a generic
point. The coefficients, and hence all masses, are transported by the same map. -/
def ofAlgHom (mass : Fin n → K) (f : MvPolynomial (Coordinate n) K →ₐ[K] L)
    (hf : ∀ e, f (equations mass e) = 0) :
    NormalizedSystem L n (fun i => algebraMap K L (mass i)) where
  x i := f (X (xCoord i))
  y i := f (X (yCoord i))
  delta i j := f (X (deltaCoord i j))
  delta_symm i j := by
    by_cases hij : i = j
    · subst j; rfl
    · have h := hf (.inr (.inl (i, j)))
      simpa [equations, symmetry, hij, sub_eq_zero] using h
  delta_diagonal i := by
    simpa [equations, symmetry] using hf (.inr (.inl (i, i)))
  force_x i := by
    have hC (c : K) : f (C c) = algebraMap K L c := f.commutes c
    simpa [equations, forceX, hC, sub_eq_zero] using hf (.inl (.inl i))
  force_y i := by
    have hC (c : K) : f (C c) = algebraMap K L c := f.commutes c
    simpa [equations, forceY, hC, sub_eq_zero] using hf (.inl (.inr i))
  distance i j hij := by
    simpa [equations, distance, hij, squaredSeparation, sub_eq_zero] using
      hf (.inr (.inr (i, j)))

def potentialPolynomial (mass : Fin n → K) : MvPolynomial (Coordinate n) K :=
  ∑ i, ∑ j, if i < j then C (mass i) * C (mass j) * X (deltaCoord i j) else 0

theorem map_potentialPolynomial (mass : Fin n → K)
    (f : MvPolynomial (Coordinate n) K →ₐ[K] L)
    (hf : ∀ e, f (equations mass e) = 0) :
    f (potentialPolynomial mass) = (ofAlgHom mass f hf).unorderedPotential := by
  have hC (c : K) : f (C c) = algebraMap K L c := f.commutes c
  simp [potentialPolynomial, NormalizedSystem.unorderedPotential, ofAlgHom, apply_ite, hC]

def solutionIdeal (mass : Fin n → K) : Ideal (MvPolynomial (Coordinate n) K) :=
  Ideal.span (Set.range (equations mass))

theorem equation_mem_solutionIdeal (mass : Fin n → K) (e : Equation n) :
    equations mass e ∈ solutionIdeal mass := Ideal.subset_span ⟨e, rfl⟩

theorem solutionIdeal_le_eval_ker (mass : Fin n → K)
    (q : NormalizedSystem K n mass) :
    solutionIdeal mass ≤ RingHom.ker (MvPolynomial.aeval (assignment q)) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨e, rfl⟩
  exact normalized_vanishes q e

theorem eval_potentialPolynomial (mass : Fin n → K) (q : NormalizedSystem K n mass) :
    MvPolynomial.aeval (assignment q) (potentialPolynomial mass) = q.unorderedPotential := by
  simp [potentialPolynomial, NormalizedSystem.unorderedPotential, apply_ite, assignment, deltaCoord]

end PolynomialEncoding

namespace NormalizedSystem

open PolynomialEncoding

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] {n : ℕ}

/-- Generic stationarity holds on every prime component, not merely at the
smooth complex points of a component. -/
theorem potential_constant_mod_prime (mass : Fin n → K)
    (P : Ideal (MvPolynomial (Coordinate n) K)) [P.IsPrime]
    (hP : solutionIdeal mass ≤ P) :
    ∃ c : K, potentialPolynomial mass - algebraMap K (MvPolynomial (Coordinate n) K) c ∈ P := by
  let R := MvPolynomial (Coordinate n) K
  let L := FractionRing (R ⧸ P)
  letI : Module L L := Semiring.toModule
  letI : Algebra ℤ L := Ring.toIntAlgebra L
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  let f : R →ₐ[K] L :=
    (IsScalarTower.toAlgHom K (R ⧸ P) L).comp (Ideal.Quotient.mkₐ K P)
  have hf : ∀ e, f (equations mass e) = 0 := by
    intro e
    change algebraMap (R ⧸ P) L (Ideal.Quotient.mk P (equations mass e)) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hP (equation_mem_solutionIdeal mass e)), map_zero]
  let q := ofAlgHom mass f hf
  apply exists_scalar_mod_prime_of_all_derivations_zero (L := L) P (potentialPolynomial mass)
  intro D hD
  change D (f (potentialPolynomial mass)) = 0
  rw [map_potentialPolynomial mass f hf]
  exact q.derivation_unorderedPotential_eq_zero D (fun i => hD (mass i))

/-- Chang's Lemma 2.2, for fixed masses over any algebraically closed field of
characteristic zero. No finiteness of configurations is assumed. -/
theorem finite_potential_values (mass : Fin n → K) :
    (Set.range (fun q : NormalizedSystem K n mass => q.unorderedPotential)).Finite := by
  have h := finite_values_of_constant_mod_minimal_primes
    (solutionIdeal mass) (potentialPolynomial mass) (fun P hP => by
      haveI : P.IsPrime := Ideal.minimalPrimes_isPrime hP
      exact potential_constant_mod_prime mass P hP.1.2)
  apply h.subset
  rintro _ ⟨q, rfl⟩
  exact ⟨MvPolynomial.aeval (assignment q), solutionIdeal_le_eval_ker mass q,
    eval_potentialPolynomial mass q⟩

end NormalizedSystem

end
end CentralConfigurations
