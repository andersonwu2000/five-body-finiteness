import CentralConfigurations.Enumeration.MatchingSearch
import CentralConfigurations.Enumeration.BitMasks
import Mathlib.Data.BitVec

/-!
# Small witnesses for exhaustive monochrome coverage

The producer may search for a failed rule or for an orbit representative.
The trusted part checks the supplied witness against the original rules.
No assertion made by the producer is used as a mathematical assumption.
-/

namespace CentralConfigurations

open scoped BigOperators

inductive MonoRejection (n : ℕ) where
  | column (j : Fin n)
  | zero
  | traceOne
  | traceTwo (i j : Fin n)
  | triangle (i j k : Fin n)
  | quadrilateral (i j k r : Fin n)
  | traceThree (i j k r : Fin n)
  | cut (s : Finset (Fin n))

def MonoRejection.holds {n : ℕ} (A : Fin n → Fin n → ℕ) : MonoRejection n → Prop
  | .column j => (∑ i, A i j) = 1
  | .zero => ∀ j, (∑ i, A i j) = 0
  | .traceOne => (∑ i, A i i) = 1
  | .traceTwo i j => ¬ (i ≠ j → (∑ k, A k k) = 2 → A i i = 1 → A j j = 1 →
      A i j = 1 ∧ ∀ k, k ≠ i → k ≠ j → A i k = A j k)
  | .triangle i j k => ¬ (i ≠ j → i ≠ k → j ≠ k →
      (A i i + A j j + A k k) * (A i i + A i j + A i k) *
        (A i k + A j k + A k k) * (A i j + A j j + A j k) ≠ 16 ∧
      (A i i + A i j + A i k + A j j + A j k + A k k) *
        max (A i i + A i j + A i k)
          (max (A i j + A j j + A j k) (A i k + A j k + A k k)) ≠ 9)
  | .quadrilateral i j k r => ¬ (i ≠ j → i ≠ k → i ≠ r → j ≠ k → j ≠ r → k ≠ r →
      A i j + A i k + A i r + A j k + A j r + A k r ≠ 5)
  | .traceThree i j k r => ¬ (i ≠ j → i ≠ k → j ≠ k → r ≠ i → r ≠ j → r ≠ k →
      (∑ a, A a a) = 3 → A i i = 1 → A j j = 1 → A k k = 1 →
      A i j = 1 → A i k = 1 → A i r = 1 → A j r + A k r ≠ 0)
  | .cut s => ¬ ((∀ i ∈ s, A i i = 0) → (∑ i ∈ s, ∑ j ∈ sᶜ, A i j) ≠ 1)

set_option synthInstance.maxSize 4096 in
instance {n : ℕ} (A : Fin n → Fin n → ℕ) (w : MonoRejection n) :
    Decidable (w.holds A) := by
  cases w <;> unfold MonoRejection.holds <;> infer_instance

theorem MonoRejection.excludes {n : ℕ} {A : Fin n → Fin n → ℕ}
    (w : MonoRejection n) (hw : w.holds A) : ¬ MonochromeConditions A := by
  rintro ⟨hcol, hnonzero, ht, ht2, htri, hquad, ht3, hcut⟩
  cases w with
  | column j => exact hcol j hw
  | zero => obtain ⟨j, hj⟩ := hnonzero; exact hj (hw j)
  | traceOne => exact ht hw
  | traceTwo i j => exact hw (ht2 i j)
  | triangle i j k => exact hw (htri i j k)
  | quadrilateral i j k r => exact hw (hquad i j k r)
  | traceThree i j k r => exact hw (ht3 i j k r)
  | cut s => exact hw (hcut s)

/-- Check the forward map alone; finiteness supplies its inverse in the proof. -/
def monoOrbitWitness {n : ℕ} (c r : BinaryMatrixCode n) (e : Fin n → Fin n) : Prop :=
  Function.Injective e ∧ ∀ p : UpperIndex n, c (upperIndex (e p.1.1) (e p.1.2)) = r p

instance {n : ℕ} (c r : BinaryMatrixCode n) (e : Fin n → Fin n) :
    Decidable (monoOrbitWitness c r e) := by
  unfold monoOrbitWitness Function.Injective
  infer_instance

theorem monoOrbitWitness_sound {n : ℕ} {c r : BinaryMatrixCode n} {e : Fin n → Fin n}
    (h : monoOrbitWitness c r e) : ∃ f : Equiv.Perm (Fin n), BinaryMatrixCode.relabel c f = r := by
  let f : Equiv.Perm (Fin n) := Equiv.ofBijective e (Finite.injective_iff_bijective.mp h.1)
  refine ⟨f, ?_⟩
  funext p
  change decide ((if c (upperIndex (e p.1.1) (e p.1.2)) then 1 else 0) = 1) = r p
  simp only [h.2 p]
  cases r p <;> rfl

/-- A list certificate visits consecutive indices, so it cannot silently skip one. -/
def consecutiveCheck (check : ℕ → ℕ → Bool) : ℕ → List ℕ → Bool
  | _, [] => true
  | start, w :: ws => check start w && consecutiveCheck check (start + 1) ws

theorem consecutiveCheck_sound {check : ℕ → ℕ → Bool} {P : ℕ → Prop}
    (sound : ∀ i w, check i w = true → P i) (start : ℕ) (ws : List ℕ)
    (h : consecutiveCheck check start ws = true) :
    ∀ i, start ≤ i → i < start + ws.length → P i := by
  induction ws generalizing start with
  | nil => intro i hi hil; simp only [List.length_nil] at hil; omega
  | cons w ws ih =>
    simp only [consecutiveCheck, Bool.and_eq_true] at h
    intro i hi hil
    by_cases he : i = start
    · subst i; exact sound start w h.1
    · apply ih (start + 1) h.2 i <;> simp only [List.length_cons] at hil <;> omega

end CentralConfigurations
