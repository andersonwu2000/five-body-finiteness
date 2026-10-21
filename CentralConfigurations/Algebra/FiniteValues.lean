import CentralConfigurations.Algebra.DerivationExtension
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.EssentialFiniteness

/-!
# Finite values from generic-point stationarity

This is the algebraic finite-critical-values argument used for Chang's
Lemma 2.2. A function annihilated by all ground-field-fixing derivations
at a generic point is algebraic, hence constant over an algebraically
closed ground field. The finitely many minimal primes then bound the
values at every actual solution, including singular points.
-/

namespace CentralConfigurations

noncomputable section

open Polynomial

theorem exists_scalar_of_isAlgebraic
    {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
    (u : L) (hu : IsAlgebraic K u) : ∃ c : K, algebraMap K L c = u := by
  refine ⟨-(minpoly K u).coeff 0, ?_⟩
  have hq : (minpoly K u).leadingCoeff = 1 := minpoly.monic hu.isIntegral
  have h : (minpoly K u).degree = 1 :=
    IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hu.isIntegral)
  have he : aeval u (minpoly K u) = 0 := minpoly.aeval K u
  rw [eq_X_add_C_of_degree_eq_one h, hq, C_1, one_mul, aeval_add, aeval_X,
    aeval_C, add_eq_zero_iff_eq_neg] at he
  simpa using he.symm

theorem exists_scalar_of_all_derivations_zero
    {K L : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    [Field L] [Algebra K L] [Algebra.EssFiniteType K L]
    (u : L)
    (hu : ∀ D : Derivation ℤ L L, (∀ c : K, D (algebraMap K L c) = 0) → D u = 0) :
    ∃ c : K, algebraMap K L c = u :=
  exists_scalar_of_isAlgebraic u (isAlgebraic_of_all_derivations_zero u hu)

/-- Descend constancy in the fraction field back to membership in a prime.
No assumption of smoothness or reducedness of the solution ideal is used. -/
theorem exists_scalar_mod_prime_of_all_derivations_zero
    {K R L : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    [CommRing R] [Algebra K R] [Algebra.EssFiniteType K R]
    (P : Ideal R) [P.IsPrime] [Field L] [Algebra K L] [Algebra (R ⧸ P) L]
    [IsScalarTower K (R ⧸ P) L] [IsFractionRing (R ⧸ P) L] (p : R)
    (hp : ∀ D : Derivation ℤ L L,
      (∀ c : K, D (algebraMap K L c) = 0) →
      D (algebraMap (R ⧸ P) L (Ideal.Quotient.mk P p)) = 0) :
    ∃ c : K, p - algebraMap K R c ∈ P := by
  haveI : Algebra.EssFiniteType (R ⧸ P) L :=
    Algebra.EssFiniteType.of_isLocalization L (nonZeroDivisors (R ⧸ P))
  haveI : Algebra.EssFiniteType K L := Algebra.EssFiniteType.comp K (R ⧸ P) L
  obtain ⟨c, hc⟩ := exists_scalar_of_all_derivations_zero
    (K := K) (algebraMap (R ⧸ P) L (Ideal.Quotient.mk P p)) hp
  refine ⟨c, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  apply IsFractionRing.injective (R ⧸ P) L
  simpa only [map_sub, map_zero, ← IsScalarTower.algebraMap_apply,
    ← Ideal.Quotient.algebraMap_eq] using sub_eq_zero.mpr hc.symm

/-- If a polynomial is constant modulo every minimal prime of the solution
ideal, all its values on ground-field points lie in a finite set. -/
theorem finite_values_of_constant_mod_minimal_primes
    {K R : Type*} [Field K] [CommRing R] [Algebra K R] [IsNoetherianRing R]
    (I : Ideal R) (p : R)
    (hp : ∀ P ∈ I.minimalPrimes, ∃ c : K, p - algebraMap K R c ∈ P) :
    {c : K | ∃ f : R →ₐ[K] K, I ≤ RingHom.ker f ∧ f p = c}.Finite := by
  classical
  letI : Fintype I.minimalPrimes := (Ideal.finite_minimalPrimes_of_isNoetherianRing R I).fintype
  choose c hc using fun P : I.minimalPrimes => hp P.val P.property
  apply (Set.finite_range c).subset
  rintro a ⟨f, hf, rfl⟩
  haveI : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  obtain ⟨P, hP, hPf⟩ := Ideal.exists_minimalPrimes_le hf
  refine ⟨⟨P, hP⟩, ?_⟩
  have hzero : f (p - algebraMap K R (c ⟨P, hP⟩)) = 0 := hPf (hc ⟨P, hP⟩)
  have he : f p = c ⟨P, hP⟩ := by
    simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
      sub_eq_zero] using hzero
  exact he.symm

end
end CentralConfigurations
