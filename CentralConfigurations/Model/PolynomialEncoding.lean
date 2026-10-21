import CentralConfigurations.Model.Normalized
import CentralConfigurations.Algebra.Certificates

/-!
# Explicit polynomial equations for normalized configurations

This redundant-coordinate encoding stores both delta_ij and delta_ji and adds
symmetry equations. Diagonal delta entries are fixed to zero, preventing
spurious free parameters in subsequent finiteness statements.
The two constructions prove soundness and completeness of the encoding, before
the separate rotational gauge is imposed. This is equation (2.2), not a model
for leading terms of singular sequences.
-/

namespace CentralConfigurations.PolynomialEncoding

noncomputable section

open scoped BigOperators
open MvPolynomial

abbrev Coordinate (n : ℕ) := Fin n ⊕ (Fin n ⊕ (Fin n × Fin n))
abbrev Equation (n : ℕ) := (Fin n ⊕ Fin n) ⊕ ((Fin n × Fin n) ⊕ (Fin n × Fin n))

variable {K : Type*} [CommRing K] {n : ℕ}

def xCoord (i : Fin n) : Coordinate n := .inl i
def yCoord (i : Fin n) : Coordinate n := .inr (.inl i)
def deltaCoord (i j : Fin n) : Coordinate n := .inr (.inr (i, j))

def forceX (mass : Fin n → K) (i : Fin n) : MvPolynomial (Coordinate n) K :=
  X (xCoord i) - ∑ j, C (mass j) * X (deltaCoord i j) ^ 3 *
    (X (xCoord i) - X (xCoord j))

def forceY (mass : Fin n → K) (i : Fin n) : MvPolynomial (Coordinate n) K :=
  X (yCoord i) - ∑ j, C (mass j) * X (deltaCoord i j) ^ 3 *
    (X (yCoord i) - X (yCoord j))

def symmetry (i j : Fin n) : MvPolynomial (Coordinate n) K :=
  if i = j then X (deltaCoord i i) else X (deltaCoord i j) - X (deltaCoord j i)

def distance (i j : Fin n) : MvPolynomial (Coordinate n) K :=
  if i = j then 0 else
    X (deltaCoord i j) ^ 2 *
      ((X (xCoord i) - X (xCoord j)) ^ 2 +
       (X (yCoord i) - X (yCoord j)) ^ 2) - 1

def equations (mass : Fin n → K) : Equation n → MvPolynomial (Coordinate n) K
  | .inl (.inl i) => forceX mass i
  | .inl (.inr i) => forceY mass i
  | .inr (.inl (i, j)) => symmetry i j
  | .inr (.inr (i, j)) => distance i j

def assignment {mass : Fin n → K} (q : NormalizedSystem K n mass) : Coordinate n → K
  | .inl i => q.x i
  | .inr (.inl i) => q.y i
  | .inr (.inr (i, j)) => q.delta i j

/-- Every solution of (2.2) satisfies every polynomial in the encoding. -/
theorem normalized_vanishes {mass : Fin n → K} (q : NormalizedSystem K n mass) :
    ∀ e, eval (assignment q) (equations mass e) = 0 := by
  intro e
  rcases e with (i | i) | (⟨i, j⟩ | ⟨i, j⟩)
  · simpa [equations, forceX, assignment, xCoord, deltaCoord] using
      sub_eq_zero.mpr (q.force_x i)
  · simpa [equations, forceY, assignment, yCoord, deltaCoord] using
      sub_eq_zero.mpr (q.force_y i)
  · by_cases hij : i = j
    · subst j
      simpa [equations, symmetry, assignment, deltaCoord] using q.delta_diagonal i
    · simpa [equations, symmetry, hij, assignment, deltaCoord] using
        sub_eq_zero.mpr (q.delta_symm i j)
  · by_cases hij : i = j
    · simp [equations, distance, hij]
    · simpa [equations, distance, hij, assignment, deltaCoord, xCoord, yCoord,
        squaredSeparation] using sub_eq_zero.mpr (q.distance i j hij)

/-- Conversely, a common zero supplies an actual normalized system. -/
def ofCommonZero (mass : Fin n → K) (a : Coordinate n → K)
    (ha : ∀ e, eval a (equations mass e) = 0) : NormalizedSystem K n mass where
  x i := a (xCoord i)
  y i := a (yCoord i)
  delta i j := a (deltaCoord i j)
  delta_symm i j := by
    by_cases hij : i = j
    · subst j
      rfl
    · have h := ha (.inr (.inl (i, j)))
      simpa [equations, symmetry, hij, sub_eq_zero] using h
  delta_diagonal i := by
    have h := ha (.inr (.inl (i, i)))
    simpa [equations, symmetry] using h
  force_x i := by
    have h := ha (.inl (.inl i))
    simpa [equations, forceX, sub_eq_zero] using h
  force_y i := by
    have h := ha (.inl (.inr i))
    simpa [equations, forceY, sub_eq_zero] using h
  distance i j hij := by
    have h := ha (.inr (.inr (i, j)))
    simpa [equations, distance, hij, squaredSeparation, sub_eq_zero] using h

theorem assignment_ofCommonZero (mass : Fin n → K) (a : Coordinate n → K)
    (ha : ∀ e, eval a (equations mass e) = 0) : assignment (ofCommonZero mass a ha) = a := by
  funext v
  rcases v with i | (i | ⟨i, j⟩) <;> rfl

theorem ofCommonZero_assignment {mass : Fin n → K} (q : NormalizedSystem K n mass) :
    ofCommonZero mass (assignment q) (normalized_vanishes q) = q := by
  cases q
  rfl

/-- The encoding is a bijection, so it cannot change solution-set cardinality. -/
def commonZeroEquiv (mass : Fin n → K) :
    NormalizedSystem K n mass ≃ {a : Coordinate n → K // ∀ e, eval a (equations mass e) = 0} where
  toFun q := ⟨assignment q, normalized_vanishes q⟩
  invFun a := ofCommonZero mass a.val a.property
  left_inv := ofCommonZero_assignment
  right_inv a := by
    apply Subtype.ext
    exact assignment_ofCommonZero mass a.val a.property

/-- This connects the polynomial certificate interface to the original model. -/
theorem certificate_consequence {mass : Fin n → K} (q : NormalizedSystem K n mass)
    {p : MvPolynomial (Coordinate n) K}
    (c : Certificate.IdealCombination (equations mass) p) :
    eval (assignment q) p = 0 := c.sound _ (normalized_vanishes q)

end
end CentralConfigurations.PolynomialEncoding
