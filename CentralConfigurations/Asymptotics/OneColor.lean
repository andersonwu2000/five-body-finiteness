import CentralConfigurations.Model.ZW
import CentralConfigurations.Model.Invariance
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Monoid

/-!
# Leading-order balance and the algebraic part of one-color rules

Chang (2023), Theorem 2.5 (Rules 1a, 1c, and part of 1d). This file proves
the balance rules from limits of scaled force equations, rather than making
the rules part of the definition of an admissible diagram. Subsequence
extraction and normalization with a nonzero limiting component remain separate.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

structure OneColorLimit (K : Type*) [CommRing K] (n : ℕ) (mass : Fin n → K) where
  position : Fin n → K
  force : Fin n → Fin n → K
  diagonal : ∀ i, force i i = 0
  antisymm : ∀ i j, force i j = -force j i
  balance : ∀ i, position i = ∑ j, mass j * force i j

/-- The scaled equation at each index of a sequence, before taking its limit. -/
def ZWSystem.scaledZ {K : Type*} [CommRing K] {n : ℕ} {mass : Fin n → K}
    (q : ZWSystem K n mass) (a : K) : OneColorLimit K n mass where
  position i := a * q.z i
  force i j := a * q.delta i j ^ 3 * (q.z i - q.z j)
  diagonal i := by simp
  antisymm i j := by rw [q.delta_symm i j]; ring
  balance i := by
    calc
      _ = a * (∑ j, mass j * q.delta i j ^ 3 * (q.z i - q.z j)) := by
        rw [← q.force_z i]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- Limits preserve the complete finite balance system. -/
def OneColorLimit.ofLimit {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → OneColorLimit ℂ n mass) (p : Fin n → ℂ) (f : Fin n → Fin n → ℂ)
    (hp : ∀ i, Tendsto (fun t => (q t).position i) atTop (𝓝 (p i)))
    (hf : ∀ i j, Tendsto (fun t => (q t).force i j) atTop (𝓝 (f i j))) :
    OneColorLimit ℂ n mass where
  position := p
  force := f
  diagonal i := by
    have h := hf i i
    simp_rw [(q _).diagonal] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  antisymm i j := by
    have h := (hf j i).neg
    have heq : (fun t => -(q t).force j i) = (fun t => (q t).force i j) :=
      funext fun t => ((q t).antisymm i j).symm
    rw [heq] at h
    exact tendsto_nhds_unique (hf i j) h
  balance i := by
    have h : Tendsto (fun t => ∑ j, mass j * (q t).force i j) atTop
        (𝓝 (∑ j, mass j * f i j)) :=
      tendsto_finsetSum Finset.univ (fun j _ => tendsto_const_nhds.mul (hf i j))
    have heq : (fun t => ∑ j, mass j * (q t).force i j) =
        (fun t => (q t).position i) := funext fun t => ((q t).balance i).symm
    rw [heq] at h
    exact tendsto_nhds_unique (hp i) h

theorem OneColorLimit.circle_has_stroke {K : Type*} [CommRing K]
    {n : ℕ} {mass : Fin n → K} (q : OneColorLimit K n mass) (i : Fin n)
    (hi : q.position i ≠ 0) : ∃ j, j ≠ i ∧ q.force i j ≠ 0 := by
  classical
  by_contra hn
  have hz : ∀ j, q.force i j = 0 := by
    intro j
    by_contra h
    exact hn ⟨j, (fun hji => h (hji ▸ q.diagonal i)), h⟩
  apply hi
  rw [q.balance i]
  simp [hz]

/-- At a stroke endpoint with no second stroke there must be a circle. -/
theorem OneColorLimit.single_stroke_circled {K : Type*} [CommRing K] [IsDomain K]
    {n : ℕ} {mass : Fin n → K} (q : OneColorLimit K n mass) (i j : Fin n)
    (hm : mass j ≠ 0) (hf : q.force i j ≠ 0)
    (hother : ∀ k, k ≠ j → q.force i k = 0) : q.position i ≠ 0 := by
  rw [q.balance i, Finset.sum_eq_single j]
  · exact mul_ne_zero hm hf
  · intro k _ hkj
    rw [hother k hkj, mul_zero]
  · simp

theorem antisymmetric_sum_zero {K ι : Type*} [CommRing K] [IsDomain K] [CharZero K]
    (s : Finset ι) (f : ι → ι → K)
    (hf : ∀ i ∈ s, ∀ j ∈ s, f i j = -f j i) :
    (∑ i ∈ s, ∑ j ∈ s, f i j) = 0 := by
  apply CharZero.eq_neg_self_iff.mp
  rw [← Finset.sum_neg_distrib]
  calc
    _ = ∑ j ∈ s, ∑ i ∈ s, f i j := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      exact hf i hi j hj

/-- An isolated set of vertices has zero leading mass center (Rule 1c). -/
theorem OneColorLimit.component_balance {K : Type*} [CommRing K] [IsDomain K] [CharZero K]
    {n : ℕ} {mass : Fin n → K} (q : OneColorLimit K n mass) (s : Finset (Fin n))
    (hclosed : ∀ i ∈ s, ∀ j, j ∉ s → q.force i j = 0) :
    (∑ i ∈ s, mass i * q.position i) = 0 := by
  have hrestrict (i : Fin n) (hi : i ∈ s) :
      (∑ j, mass j * q.force i j) = ∑ j ∈ s, mass j * q.force i j := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hjs
    rw [hclosed i hi j hjs, mul_zero]
  calc
    _ = ∑ i ∈ s, ∑ j ∈ s, mass i * mass j * q.force i j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [q.balance i, hrestrict i hi, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = 0 := antisymmetric_sum_zero s _ (by
      intro i _ j _
      rw [q.antisymm i j]
      ring)

/-- In an isolated component a unique circle is impossible (first part of Rule 1d). -/
theorem OneColorLimit.no_unique_component_circle {K : Type*} [CommRing K] [IsDomain K]
    [CharZero K] {n : ℕ} {mass : Fin n → K} (q : OneColorLimit K n mass)
    (s : Finset (Fin n)) (i : Fin n) (hi : i ∈ s) (hm : mass i ≠ 0)
    (hclosed : ∀ j ∈ s, ∀ k, k ∉ s → q.force j k = 0)
    (hother : ∀ j ∈ s, j ≠ i → q.position j = 0) : q.position i = 0 := by
  have h := q.component_balance s hclosed
  rw [Finset.sum_eq_single i] at h
  · exact (mul_eq_zero.mp h).resolve_left hm
  · intro j hj hji
    rw [hother j hj hji, mul_zero]
  · exact fun hni => (hni hi).elim

/-- The nonzero leading positions in an isolated component cannot all coincide
when every nonempty subsystem has nonzero total mass (second part of Rule 1d). -/
theorem OneColorLimit.coincident_component_circles_zero {K : Type*} [CommRing K]
    [IsDomain K] [CharZero K] {n : ℕ} {mass : Fin n → K}
    (q : OneColorLimit K n mass) (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (i : Fin n) (hi : i ∈ s)
    (hclosed : ∀ j ∈ s, ∀ k, k ∉ s → q.force j k = 0)
    (hcoincident : ∀ j ∈ s, q.position j ≠ 0 → q.position j = q.position i) :
    q.position i = 0 := by
  classical
  by_contra hpi
  let circles := s.filter (fun j => q.position j ≠ 0)
  have hnonempty : circles.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨hi, hpi⟩⟩
  have hsum : (∑ j ∈ circles, mass j) * q.position i = 0 := by
    calc
      _ = ∑ j ∈ circles, mass j * q.position i := Finset.sum_mul _ _ _
      _ = ∑ j ∈ circles, mass j * q.position j := by
        apply Finset.sum_congr rfl
        intro j hj
        have hh := Finset.mem_filter.mp hj
        rw [hcoincident j hh.1 hh.2]
      _ = ∑ j ∈ s, mass j * q.position j := by
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro j hjs hjc
        have hz : q.position j = 0 := by
          by_contra hj
          exact hjc (Finset.mem_filter.mpr ⟨hjs, hj⟩)
        rw [hz, mul_zero]
      _ = 0 := q.component_balance s hclosed
  exact mul_ne_zero (hm circles hnonempty) hpi hsum

end CentralConfigurations
