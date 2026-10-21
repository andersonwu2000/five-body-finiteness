import CentralConfigurations.Enumeration.AppendixSearch
import CentralConfigurations.Enumeration.RelabelCode

/-!
# Local rejection witnesses for the simultaneous two-color search

Each witness names one clause of the already proved matrix rules. The soundness
theorem refers to the original appendix candidate predicate; the external
producer need not be trusted to implement the complete predicate correctly.
-/

namespace CentralConfigurations

open scoped BigOperators

inductive OrientedPairRejection (n : ℕ) where
  | circling (i j : Fin n)
  | traceRows (i j k : Fin n)
  | positiveTrace (i j : Fin n)
  | component
  | star (i j k : Fin n)

def OrientedPairRejection.holds {n : ℕ} (A B : Fin n → Fin n → ℕ) :
    OrientedPairRejection n → Prop
  | .circling i j => ¬ (i ≠ j → A i j * (B i i + B j j) ≠ 1)
  | .traceRows i j k => ¬ (i ≠ j → (∑ a, A a a) = 2 → A i i = 1 → A j j = 1 →
      B i k = 0 ∧ B j k = 0)
  | .positiveTrace i j => ¬ (i ≠ j → (∑ r, A r r) = 2 → A i i = 1 → A j j = 1 →
      (∀ r, r ≠ i → r ≠ j → A i r = 0 ∧ A j r = 0) → (∑ r, B r r) ≠ n - 3)
  | .component => appendixComponentCheck A B ≠ true
  | .star i j k => ¬ (i ≠ j → i ≠ k → j ≠ k →
      A i i = 1 → A j j = 0 → A k k = 0 → A i j * A i k = 0)

set_option synthInstance.maxSize 8192 in
instance orientedPairRejection_decidable {n : ℕ} (A B : Fin n → Fin n → ℕ)
    (w : OrientedPairRejection n) :
    Decidable (w.holds A B) := by
  cases w <;> unfold OrientedPairRejection.holds <;> infer_instance

theorem OrientedPairRejection.excludes {n : ℕ} {A B : Fin n → Fin n → ℕ}
    (w : OrientedPairRejection n) (hw : w.holds A B)
    (hcir : ∀ i j, i ≠ j → A i j * (B i i + B j j) ≠ 1)
    (hrows : TraceTwoCompanionRowsRule A B) (hpos : PositiveTraceTwoExclusion A B)
    (hcomp : appendixComponentCheck A B = true) (hstar : OneCircledStarRule A) : False := by
  cases w with
  | circling i j => exact hw (hcir i j)
  | traceRows i j k => exact hw (fun hij ht hi hj => hrows i j hij ht hi hj k)
  | positiveTrace i j => exact hw (hpos i j)
  | component => exact hw hcomp
  | star i j k => exact hw (hstar i j k)

inductive PairRejection (n : ℕ) where
  | oriented (flip : Bool) (w : OrientedPairRejection n)
  | triangle (i j k : Fin n)
  | columns (i j : Fin n)
  | quadrilateral (i j k r : Fin n)
  | pentagon (v : Fin 5 → Fin n)
  | secondTrace
  | singleDouble

def PairRejection.holds {n : ℕ} (A B : Fin n → Fin n → ℕ) : PairRejection n → Prop
  | .oriented flip w => if flip then w.holds B A else w.holds A B
  | .triangle i j k => ¬ (i ≠ j → j ≠ k → i ≠ k →
      (A i j + B i j) + (A j k + B j k) + (A i k + B i k) ≠ 4 ∧
      (A i j + B i j) + (A j k + B j k) + (A i k + B i k) ≠ 5 ∧
      ((A i j + B i j) * (A j k + B j k) * (A i k + B i k) *
          max (A i j + A j k + A i k) (B i j + B j k + B i k) = 0 ∨
        (A i j + B i j) * (A j k + B j k) * (A i k + B i k) *
          max (A i j + A j k + A i k) (B i j + B j k + B i k) = 3 ∨
        (A i j + B i j) * (A j k + B j k) * (A i k + B i k) *
          max (A i j + A j k + A i k) (B i j + B j k + B i k) = 24))
  | .columns i j => ¬ (i ≠ j → A i j + B i j = 2 →
      matrixOutsidePairSum A i j * matrixOutsidePairSum B i j ≠ 0)
  | .quadrilateral i j k r => ¬ (i ≠ j → i ≠ k → i ≠ r → j ≠ k → j ≠ r → k ≠ r →
      A i j + B i j ≠ 0 → A j k + B j k ≠ 0 →
      A k r + B k r ≠ 0 → A i r + B i r ≠ 0 →
      A i j + A k r ≠ 1 ∧ A j k + A i r ≠ 1 ∧
      B i j + B k r ≠ 1 ∧ B j k + B i r ≠ 1)
  | .pentagon v => ¬ (Function.Injective v →
      (∀ k, A (v k) (v (pentagonRotation k)) + B (v k) (v (pentagonRotation k)) ≠ 0) →
      cycleZCount A B v ≠ 1 ∧ cycleWCount A B v ≠ 1 ∧
      ¬(cycleZCount A B v = 4 ∧ cycleWCount A B v = 0 ∧ cycleDoubleCount A B v = 1) ∧
      ¬(cycleZCount A B v = 0 ∧ cycleWCount A B v = 4 ∧ cycleDoubleCount A B v = 1))
  | .secondTrace => ¬ ((∀ i j, i ≠ j → A i j + B i j ≠ 1) → (∑ i, (A i i + B i i)) = 0)
  | .singleDouble => ¬ NoSingleDoubleEdgeRule A B

set_option synthInstance.maxSize 16384 in
instance pairRejection_decidable {n : ℕ} (A B : Fin n → Fin n → ℕ) (w : PairRejection n) :
    Decidable (w.holds A B) := by
  cases w <;> unfold PairRejection.holds <;> unfold Function.Injective <;> infer_instance

theorem PairRejection.excludes {n : ℕ} {A B : Fin n → Fin n → ℕ}
    (w : PairRejection n) (hw : w.holds A B) (h : BicoloredConditions A B)
    (hstarA : OneCircledStarRule A) (hstarB : OneCircledStarRule B)
    (hdouble : NoSingleDoubleEdgeRule A B) : False := by
  obtain ⟨hcirA, hcirB, hrowA, hrowB, hposA, hposB, htri, hcol,
    hquad, hpent, _, _, hcompA, hcompB, hsecond⟩ := h
  cases w with
  | oriented flip w =>
    cases flip with
    | false => exact w.excludes hw hcirA hrowA hposA hcompA hstarA
    | true => exact w.excludes hw hcirB hrowB hposB hcompB hstarB
  | triangle i j k => exact hw (htri i j k)
  | columns i j => exact hw (hcol i j)
  | quadrilateral i j k r => exact hw (hquad i j k r)
  | pentagon v => exact hw (hpent v)
  | secondTrace => exact hw hsecond
  | singleDouble => exact hw hdouble

theorem PairRejection.excludes_check {n : ℕ} {c d : BinaryMatrixCode n}
    (w : PairRejection n) (hw : w.holds (BinaryMatrixCode.decode c) (BinaryMatrixCode.decode d)) :
    appendixCandidateCheck c d ≠ true := by
  intro h
  simp only [appendixCandidateCheck, Bool.and_eq_true, candidateCheck_eq_true,
    appendixExtraCheck_eq_true] at h
  exact w.excludes hw h.1.2 h.2.1 h.2.2.1 h.2.2.2

/-- Both colors use this one forward map and this one optional color exchange. -/
def PairOrbitWitness {n : ℕ} (d r : DiagramCode n) (e : Fin n → Fin n) (flip : Bool) : Prop :=
  Function.Injective e ∧
    (∀ p, rawRelabel (if flip then d.2 else d.1) e p = r.1 p) ∧
    (∀ p, rawRelabel (if flip then d.1 else d.2) e p = r.2 p)

instance pairOrbitWitness_decidable {n : ℕ} (d r : DiagramCode n) (e : Fin n → Fin n) (flip : Bool) :
    Decidable (PairOrbitWitness d r e flip) := by
  unfold PairOrbitWitness Function.Injective
  infer_instance

theorem PairOrbitWitness.sound {n : ℕ} {d r : DiagramCode n} {e : Fin n → Fin n} {flip : Bool}
    (h : PairOrbitWitness d r e flip) : r ∈ DiagramCode.orbit d := by
  let f : Equiv.Perm (Fin n) := Equiv.ofBijective e (Finite.injective_iff_bijective.mp h.1)
  apply (DiagramCode.mem_orbit_iff d r).mpr
  refine ⟨f, flip, ?_⟩
  have hfirst := funext h.2.1
  have hsecond := funext h.2.2
  cases flip with
  | false =>
    apply Prod.ext
    · exact (rawRelabel_eq_relabel d.1 f).symm.trans hfirst
    · exact (rawRelabel_eq_relabel d.2 f).symm.trans hsecond
  | true =>
    apply Prod.ext
    · exact (rawRelabel_eq_relabel d.2 f).symm.trans hfirst
    · exact (rawRelabel_eq_relabel d.1 f).symm.trans hsecond

end CentralConfigurations
