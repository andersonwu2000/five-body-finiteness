import Mathlib.RingTheory.Smooth.Field
import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.Algebra.Polynomial.Derivation
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# Derivations detecting a transcendental value

Auxiliary algebra for the finite-critical-values argument in Chang's Lemma
2.2. Formal smoothness extends a derivation using a square-zero extension.
For an essentially finite-type characteristic-zero field extension, a
transcendental element can therefore be sent to 1 by a derivation fixing
the ground field. Consequently a value annihilated by all such derivations
is algebraic. This file does not postulate any smoothness of the possibly
singular central-configuration solution variety.
-/

namespace CentralConfigurations

open Polynomial

/-- Extend a derivation along a formally smooth algebra. The source derivation
already takes values in the target algebra; its ground ring is the integers. -/
theorem exists_derivation_extension_of_formallySmooth
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FormallySmooth A B] (D : Derivation ℤ A B) :
    ∃ E : Derivation ℤ B B, ∀ a, E (algebraMap A B a) = D a := by
  let φ : A →+* TrivSqZeroExt B B := {
    toFun := fun a => ⟨algebraMap A B a, D a⟩
    map_zero' := by ext <;> simp
    map_one' := by ext <;> simp
    map_add' := by intro a b; ext <;> simp
    map_mul' := by
      intro a b
      ext <;> simp [Derivation.leibniz, Algebra.smul_def,
        mul_comm, add_comm]
  }
  letI : Algebra A (TrivSqZeroExt B B) := φ.toAlgebra
  let π : TrivSqZeroExt B B →ₐ[A] B := {
    toRingHom := (TrivSqZeroExt.fstHom B B B).toRingHom
    commutes' := fun _ => rfl
  }
  have hπ : Function.Surjective π := TrivSqZeroExt.fst_surjective
  have hnil : IsNilpotent (RingHom.ker π) :=
    ⟨2, TrivSqZeroExt.kerIdeal_sq B B⟩
  let f : B →ₐ[A] TrivSqZeroExt B B :=
    Algebra.FormallySmooth.liftOfSurjective (AlgHom.id A B) π hπ hnil
  have hf (b : B) : (f b).fst = b :=
    Algebra.FormallySmooth.liftOfSurjective_apply (AlgHom.id A B) π hπ hnil b
  let E : Derivation ℤ B B := {
    toFun := fun b => (f b).snd
    map_add' := by intro a b; simp
    map_smul' := by intro a b; simp
    map_one_eq_zero' := by simp
    leibniz' := by
      intro a b
      simp [hf, smul_eq_mul, mul_comm, add_comm]
  }
  refine ⟨E, fun a => ?_⟩
  exact congrArg TrivSqZeroExt.snd (f.commutes a)

/-- An injective polynomial parameter may be localized and followed by a
characteristic-zero field extension. Only the latter field extension, not
the original algebraic variety, is asserted to be smooth. -/
theorem formallySmooth_polynomial_field_extension
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra K[X] L] [IsScalarTower K K[X] L] [FaithfulSMul K[X] L]
    [Algebra.EssFiniteType K L] : Algebra.FormallySmooth K[X] L := by
  letI : Algebra (RatFunc K) L := RatFunc.liftAlgebra K L
  haveI : IsScalarTower K (RatFunc K) L := IsScalarTower.of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply K K[X] L,
      IsScalarTower.algebraMap_apply K K[X] (RatFunc K)]
    exact IsScalarTower.algebraMap_apply K[X] (RatFunc K) L _
  haveI : Algebra.EssFiniteType (RatFunc K) L := Algebra.EssFiniteType.of_comp K (RatFunc K) L
  haveI : Algebra.FormallySmooth (RatFunc K) L := inferInstance
  haveI : Algebra.FormallySmooth K[X] (RatFunc K) :=
    Algebra.FormallySmooth.of_isLocalization (nonZeroDivisors K[X])
  exact Algebra.FormallySmooth.comp K[X] (RatFunc K) L

theorem exists_derivation_of_transcendental
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] (u : L) (hu : Transcendental K u) :
    ∃ D : Derivation ℤ L L, (∀ c : K, D (algebraMap K L c) = 0) ∧ D u = 1 := by
  letI : Algebra K[X] L := (Polynomial.aeval u).toRingHom.toAlgebra
  haveI : IsScalarTower K K[X] L := IsScalarTower.of_algebraMap_eq fun c => by
    simp [RingHom.algebraMap_toAlgebra]
  haveI : FaithfulSMul K[X] L :=
    (faithfulSMul_iff_algebraMap_injective K[X] L).mpr
      (transcendental_iff_injective.mp hu)
  haveI : Algebra.FormallySmooth K[X] L := formallySmooth_polynomial_field_extension
  let D : Derivation ℤ K[X] L := (Polynomial.mkDerivation K (1 : L)).restrictScalars ℤ
  obtain ⟨E, hE⟩ := exists_derivation_extension_of_formallySmooth D
  refine ⟨E, ?_, ?_⟩
  · intro c
    have hDC : D (Polynomial.C c) = 0 :=
      Polynomial.derivation_C (Polynomial.mkDerivation K (1 : L)) c
    have h := (hE (Polynomial.C c)).trans hDC
    simpa [RingHom.algebraMap_toAlgebra] using h
  · have hDX : D Polynomial.X = 1 := Polynomial.mkDerivation_X K (1 : L)
    have h := (hE Polynomial.X).trans hDX
    simpa [RingHom.algebraMap_toAlgebra] using h

theorem isAlgebraic_of_all_derivations_zero
    {K L : Type*} [Field K] [CharZero K] [Field L] [Algebra K L]
    [Algebra.EssFiniteType K L] (u : L)
    (hu : ∀ D : Derivation ℤ L L, (∀ c : K, D (algebraMap K L c) = 0) → D u = 0) :
    IsAlgebraic K u := by
  by_contra h
  obtain ⟨D, hD, hDu⟩ := exists_derivation_of_transcendental u h
  exact zero_ne_one ((hu D hD).symm.trans hDu)

end CentralConfigurations
