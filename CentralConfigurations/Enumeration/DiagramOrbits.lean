import CentralConfigurations.Enumeration.BinaryMatrices
import Mathlib.Data.Fintype.Perm
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Simultaneous relabeling and color exchange

Diagram equivalence uses a common permutation of both colors, optionally
followed by color exchange. Sorting the first diagonal transports the second
matrix by the same permutation. The coverage checker verifies a given finite
candidate list; concrete lists are certified in the enumeration modules.
-/

namespace CentralConfigurations

open scoped BigOperators

abbrev DiagramCode (n : ℕ) := BinaryMatrixCode n × BinaryMatrixCode n

namespace BinaryMatrixCode

def trace {n : ℕ} (c : BinaryMatrixCode n) : ℕ := ∑ i, decode c i i

@[simp] theorem trace_relabel {n : ℕ} (c : BinaryMatrixCode n) (e : Equiv.Perm (Fin n)) :
    trace (relabel c e) = trace c := by
  simp only [trace, decode_relabel]
  exact Equiv.sum_comp e (fun i => decode c i i)

end BinaryMatrixCode

namespace DiagramCode

def relabel {n : ℕ} (d : DiagramCode n) (e : Equiv.Perm (Fin n)) : DiagramCode n :=
  (BinaryMatrixCode.relabel d.1 e, BinaryMatrixCode.relabel d.2 e)

def swap {n : ℕ} (d : DiagramCode n) : DiagramCode n := (d.2, d.1)

def transform {n : ℕ} (d : DiagramCode n) (e : Equiv.Perm (Fin n)) (flip : Bool) :
    DiagramCode n := if flip then swap (relabel d e) else relabel d e

@[simp] theorem relabel_refl {n : ℕ} (d : DiagramCode n) : relabel d (Equiv.refl _) = d := by
  simp [relabel]

theorem relabel_relabel {n : ℕ} (d : DiagramCode n) (e f : Equiv.Perm (Fin n)) :
    relabel (relabel d e) f = relabel d (f.trans e) := by
  simp [relabel, BinaryMatrixCode.relabel_relabel]

@[simp] theorem swap_swap {n : ℕ} (d : DiagramCode n) : swap (swap d) = d := rfl

theorem swap_relabel {n : ℕ} (d : DiagramCode n) (e : Equiv.Perm (Fin n)) :
    swap (relabel d e) = relabel (swap d) e := rfl

theorem transform_transform {n : ℕ} (d : DiagramCode n) (e f : Equiv.Perm (Fin n))
    (s t : Bool) : transform (transform d e s) f t = transform d (f.trans e) (s.xor t) := by
  cases s <;> cases t <;> simp [transform, relabel, swap, BinaryMatrixCode.relabel_relabel]

@[simp] theorem transform_inverse {n : ℕ} (d : DiagramCode n) (e : Equiv.Perm (Fin n))
    (s : Bool) : transform (transform d e s) e.symm s = d := by
  cases s <;> simp [transform, relabel, swap]

def orbit {n : ℕ} (d : DiagramCode n) : Finset (DiagramCode n) :=
  Finset.univ.image (fun p : Equiv.Perm (Fin n) × Bool => transform d p.1 p.2)

theorem mem_orbit_iff {n : ℕ} (d r : DiagramCode n) :
    r ∈ orbit d ↔ ∃ e : Equiv.Perm (Fin n), ∃ s : Bool, transform d e s = r := by
  simp [orbit]

theorem mem_own_orbit {n : ℕ} (d : DiagramCode n) : d ∈ orbit d :=
  (mem_orbit_iff d d).mpr ⟨Equiv.refl _, false, by simp [transform]⟩

theorem orbit_symmetric {n : ℕ} {d r : DiagramCode n} (h : r ∈ orbit d) : d ∈ orbit r := by
  obtain ⟨e, s, rfl⟩ := (mem_orbit_iff d r).mp h
  exact (mem_orbit_iff _ _).mpr ⟨e.symm, s, transform_inverse d e s⟩

theorem orbit_transitive {n : ℕ} {d r u : DiagramCode n}
    (hdr : r ∈ orbit d) (hru : u ∈ orbit r) : u ∈ orbit d := by
  obtain ⟨e, s, rfl⟩ := (mem_orbit_iff d r).mp hdr
  obtain ⟨f, t, rfl⟩ := (mem_orbit_iff _ u).mp hru
  exact (mem_orbit_iff _ _).mpr ⟨f.trans e, s.xor t, (transform_transform d e f s t).symm⟩

def orient {n : ℕ} (d : DiagramCode n) : DiagramCode n :=
  if BinaryMatrixCode.trace d.1 ≤ BinaryMatrixCode.trace d.2 then d else swap d

def normalize {n : ℕ} (d : DiagramCode n) : DiagramCode n :=
  relabel (orient d) (BinaryMatrixCode.sortDiagonal (orient d).1)

theorem orient_trace_order {n : ℕ} (d : DiagramCode n) :
    BinaryMatrixCode.trace (orient d).1 ≤ BinaryMatrixCode.trace (orient d).2 := by
  unfold orient
  split_ifs with h
  · exact h
  · exact le_of_not_ge h

theorem normalize_trace_order {n : ℕ} (d : DiagramCode n) :
    BinaryMatrixCode.trace (normalize d).1 ≤ BinaryMatrixCode.trace (normalize d).2 := by
  simpa only [normalize, relabel, BinaryMatrixCode.trace_relabel] using orient_trace_order d

theorem normalize_mem_orbit {n : ℕ} (d : DiagramCode n) : normalize d ∈ orbit d := by
  apply (mem_orbit_iff _ _).mpr
  by_cases h : BinaryMatrixCode.trace d.1 ≤ BinaryMatrixCode.trace d.2
  · exact ⟨BinaryMatrixCode.sortDiagonal d.1, false, by simp [normalize, orient, transform, h]⟩
  · exact ⟨BinaryMatrixCode.sortDiagonal d.2, true, by
      simp [normalize, orient, transform, relabel, swap, h]⟩

theorem normalized_first_generated {n : ℕ} (d : DiagramCode n) :
    (normalize d).1 ∈ BinaryMatrixCode.prefixCandidates n :=
  BinaryMatrixCode.normalized_mem_prefixCandidates (orient d).1

/-- The unfiltered matching space respects (6.1) and (6.2). Monochrome
filtering and orbit reduction refine this space in the actual search. -/
def normalizedCandidates (n : ℕ) : Finset (DiagramCode n) :=
  ((BinaryMatrixCode.prefixCandidates n).product Finset.univ).filter
    (fun d => BinaryMatrixCode.trace d.1 ≤ BinaryMatrixCode.trace d.2)

theorem normalize_mem_candidates {n : ℕ} (d : DiagramCode n) :
    normalize d ∈ normalizedCandidates n := by
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨normalized_first_generated d, Finset.mem_univ _⟩, normalize_trace_order d⟩

/-- Coverage of a specified finite representative list under diagram equivalence. -/
def coverageCheck {n : ℕ} (candidates representatives : Finset (DiagramCode n)) : Bool :=
  decide (∀ d ∈ candidates, ∃ r ∈ representatives, r ∈ orbit d)

theorem coverageCheck_sound {n : ℕ} {candidates representatives : Finset (DiagramCode n)}
    (h : coverageCheck candidates representatives = true)
    {d : DiagramCode n} (hd : d ∈ candidates) :
    ∃ r ∈ representatives, r ∈ orbit d := by
  have hh : ∀ d ∈ candidates, ∃ r ∈ representatives, r ∈ orbit d := by
    simpa [coverageCheck] using h
  exact hh d hd

end DiagramCode

end CentralConfigurations
