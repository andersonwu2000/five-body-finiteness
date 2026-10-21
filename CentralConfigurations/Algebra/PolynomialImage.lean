import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Polynomial images of affine algebraic sets

Algebraic ingredients for Chang's Lemma 2.1: the image of a polynomial on
a closed algebraic set is finite or cofinite. Chevalley's theorem supplies
constructibility; on the affine line finite root sets give the dichotomy.
-/

namespace CentralConfigurations

noncomputable section

open Polynomial PrimeSpectrum Topology

theorem finite_or_finite_compl_union {α : Type*} {s t : Set α}
    (hs : s.Finite ∨ sᶜ.Finite) (ht : t.Finite ∨ tᶜ.Finite) :
    (s ∪ t).Finite ∨ (s ∪ t)ᶜ.Finite := by
  rcases hs with hs | hs
  · rcases ht with ht | ht
    · exact Or.inl (hs.union ht)
    · exact Or.inr (ht.subset (Set.compl_subset_compl.mpr Set.subset_union_right))
  · exact Or.inr (hs.subset (Set.compl_subset_compl.mpr Set.subset_union_left))

variable {K : Type*} [Field K]

def polynomialPoint (a : K) : PrimeSpectrum K[X] :=
  ⟨RingHom.ker (Polynomial.evalRingHom a), RingHom.ker_isPrime _⟩

@[simp] theorem polynomialPoint_mem_ideal (a : K) (p : K[X]) :
    p ∈ (polynomialPoint a).asIdeal ↔ p.eval a = 0 := Iff.rfl

theorem polynomialPoint_mem_basicConstructible (a : K)
    (C : BasicConstructibleSetData K[X]) :
    polynomialPoint a ∈ C.toSet ↔
      (∀ i, (C.g i).eval a = 0) ∧ C.f.eval a ≠ 0 := by
  simp only [BasicConstructibleSetData.toSet, Set.mem_diff, mem_zeroLocus,
    Set.range_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe, polynomialPoint_mem_ideal]

theorem finite_or_finite_compl_basicConstructible
    (C : BasicConstructibleSetData K[X]) :
    (polynomialPoint ⁻¹' C.toSet).Finite ∨ (polynomialPoint ⁻¹' C.toSet)ᶜ.Finite := by
  classical
  by_cases hg : ∃ i, C.g i ≠ 0
  · obtain ⟨i, hi⟩ := hg
    left
    apply (Polynomial.finite_setOf_isRoot hi).subset
    intro a ha
    exact (polynomialPoint_mem_basicConstructible a C).mp ha |>.1 i
  · have hg0 : ∀ i, C.g i = 0 := by simpa using hg
    by_cases hf : C.f = 0
    · left
      have he : polynomialPoint ⁻¹' C.toSet = ∅ := by
        ext a
        simp [polynomialPoint_mem_basicConstructible, hf]
      rw [he]
      exact Set.finite_empty
    · right
      have he : (polynomialPoint ⁻¹' C.toSet)ᶜ = {a | C.f.IsRoot a} := by
        ext a
        simp [polynomialPoint_mem_basicConstructible, hg0, Polynomial.IsRoot]
      rw [he]
      exact Polynomial.finite_setOf_isRoot hf

theorem finite_or_finite_compl_constructible_line {s : Set (PrimeSpectrum K[X])}
    (hs : IsConstructible s) :
    (polynomialPoint ⁻¹' s).Finite ∨ (polynomialPoint ⁻¹' s)ᶜ.Finite := by
  classical
  obtain ⟨S, rfl⟩ := exists_constructibleSetData_iff.mpr hs
  clear hs
  induction S using Finset.induction with
  | empty =>
      left
      simp [ConstructibleSetData.toSet]
  | @insert C S hCS ih =>
      have he : polynomialPoint ⁻¹' (ConstructibleSetData.toSet (insert C S)) =
          (polynomialPoint ⁻¹' C.toSet) ∪
            (polynomialPoint ⁻¹' ConstructibleSetData.toSet S) := by
        simp [ConstructibleSetData.toSet]
      rw [he]
      exact finite_or_finite_compl_union (finite_or_finite_compl_basicConstructible C) ih

/-- Passing through prime spectra does not introduce spurious ground-field
values: a prime over a value can be extended to a maximal ideal, and the
Nullstellensatz realizes that maximal ideal by an actual point. -/
theorem polynomial_image_eq_spectrum_preimage [IsAlgClosed K]
    {σ : Type*} [Finite σ] (I : Ideal (MvPolynomial σ K)) (p : MvPolynomial σ K) :
    (fun x => MvPolynomial.aeval x p) '' MvPolynomial.zeroLocus K I =
      polynomialPoint ⁻¹' (PrimeSpectrum.comap (Polynomial.aeval p).toRingHom ''
        PrimeSpectrum.zeroLocus (I : Set (MvPolynomial σ K))) := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨MvPolynomial.pointToPoint x, ?_, ?_⟩
    · exact MvPolynomial.pointToPoint_zeroLocus_le I ⟨x, hx, rfl⟩
    · apply PrimeSpectrum.ext
      ext t
      change Polynomial.aeval p t ∈ MvPolynomial.vanishingIdeal K {x} ↔
        t.eval (MvPolynomial.aeval x p) = 0
      rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
      have he : MvPolynomial.aeval x (Polynomial.aeval p t) =
          t.eval (MvPolynomial.aeval x p) := by
        change ((MvPolynomial.aeval x).comp (Polynomial.aeval p)) t = _
        rw [← Polynomial.aeval_algHom]
        rfl
      rw [he]
  · rintro ⟨P, hP, he⟩
    obtain ⟨J, hJ, hPJ⟩ := Ideal.exists_le_maximal P.asIdeal P.isPrime.ne_top
    obtain ⟨x, hJx⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hJ
    refine ⟨x, ?_, ?_⟩
    · intro t ht
      apply (MvPolynomial.mem_vanishingIdeal_singleton_iff x t).mp
      rw [← hJx]
      exact hPJ ((PrimeSpectrum.mem_zeroLocus P _).mp hP ht)
    · have hm : Polynomial.X - Polynomial.C a ∈ (polynomialPoint a).asIdeal := by
        simp
      rw [← he] at hm
      change Polynomial.aeval p (Polynomial.X - Polynomial.C a) ∈ P.asIdeal at hm
      simp only [map_sub, Polynomial.aeval_X, Polynomial.aeval_C] at hm
      have hz := (MvPolynomial.mem_vanishingIdeal_singleton_iff x
        (p - algebraMap K (MvPolynomial σ K) a)).mp (hJx ▸ hPJ hm)
      simpa only [map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_eq_zero] using hz

/-- Chang's Lemma 2.1 over an algebraically closed field. -/
theorem polynomial_image_finite_or_cofinite [IsAlgClosed K]
    {σ : Type*} [Finite σ] (I : Ideal (MvPolynomial σ K)) (p : MvPolynomial σ K) :
    ((fun x => MvPolynomial.aeval x p) '' MvPolynomial.zeroLocus K I).Finite ∨
      ((fun x => MvPolynomial.aeval x p) '' MvPolynomial.zeroLocus K I)ᶜ.Finite := by
  let R := MvPolynomial σ K
  letI : Algebra K[X] R := (Polynomial.aeval p).toRingHom.toAlgebra
  haveI : IsScalarTower K K[X] R := IsScalarTower.of_algebraMap_eq fun c => by
    simp [RingHom.algebraMap_toAlgebra, R, MvPolynomial.algebraMap_eq]
  haveI : Algebra.FiniteType K[X] R :=
    Algebra.FiniteType.of_restrictScalars_finiteType K K[X] R
  haveI : Algebra.FinitePresentation K[X] R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have hf : (Polynomial.aeval p : K[X] →ₐ[K] R).toRingHom.FinitePresentation :=
    (RingHom.finitePresentation_algebraMap (A := K[X]) (B := R)).mpr inferInstance
  have hz : IsConstructible (PrimeSpectrum.zeroLocus (I : Set R)) := by
    apply IsConstructible.of_compl
    exact (PrimeSpectrum.isRetrocompact_zeroLocus_compl_of_fg I.fg_of_isNoetherianRing).isConstructible
      (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
  rw [polynomial_image_eq_spectrum_preimage]
  exact finite_or_finite_compl_constructible_line (PrimeSpectrum.isConstructible_comap_image hf hz)

end
end CentralConfigurations
