import CentralConfigurations.Enumeration.DiagramOrbits

/-!
# Small isomorphism-invariant fingerprints

The fingerprint is only a sufficient certificate of inequivalence: equality
of fingerprints is not asserted to imply isomorphism. All arithmetic is in
Nat. In particular, the fixed modulus needs no primality assumption.

Two rounds of neighborhood refinement, followed by a symmetric color-pair
key, distinguish the 117 transcribed six-body source figures. Their concrete
values and distinctness are checked separately by kernel computation.
-/

namespace CentralConfigurations.DiagramCode

open scoped BigOperators

def incidenceColor {n : ℕ} (d : DiagramCode n) (i j : Fin n) : ℕ :=
  BinaryMatrixCode.decode d.1 i j + 2 * BinaryMatrixCode.decode d.2 i j

@[simp] theorem incidenceColor_relabel {n : ℕ} (d : DiagramCode n)
    (e : Equiv.Perm (Fin n)) (i j : Fin n) :
    incidenceColor (relabel d e) i j = incidenceColor d (e i) (e j) := by
  simp [incidenceColor, relabel]

def refinedColor {n : ℕ} (d : DiagramCode n) : ℕ → Fin n → ℕ
  | 0, i => incidenceColor d i i
  | k + 1, i => (17 * refinedColor d k i +
      ∑ j, (incidenceColor d i j + 4 * refinedColor d k j + 1) ^ 5) % 1000003

@[simp] theorem refinedColor_relabel {n : ℕ} (d : DiagramCode n)
    (e : Equiv.Perm (Fin n)) (k : ℕ) (i : Fin n) :
    refinedColor (relabel d e) k i = refinedColor d k (e i) := by
  induction k generalizing i with
  | zero => simp [refinedColor]
  | succ k ih =>
    simp only [refinedColor, incidenceColor_relabel, ih]
    rw [Equiv.sum_comp e
      (fun j => (incidenceColor d (e i) j + 4 * refinedColor d k j + 1) ^ 5)]

def orientedFingerprint {n : ℕ} (d : DiagramCode n) : ℕ :=
  (∑ i, refinedColor d 2 i ^ 3) % 1000003

@[simp] theorem orientedFingerprint_relabel {n : ℕ} (d : DiagramCode n)
    (e : Equiv.Perm (Fin n)) :
    orientedFingerprint (relabel d e) = orientedFingerprint d := by
  simp only [orientedFingerprint, refinedColor_relabel]
  rw [Equiv.sum_comp e (fun i => refinedColor d 2 i ^ 3)]

def fingerprint {n : ℕ} (d : DiagramCode n) : ℕ × ℕ :=
  (min (orientedFingerprint d) (orientedFingerprint (swap d)),
    max (orientedFingerprint d) (orientedFingerprint (swap d)))

@[simp] theorem fingerprint_relabel {n : ℕ} (d : DiagramCode n)
    (e : Equiv.Perm (Fin n)) : fingerprint (relabel d e) = fingerprint d := by
  simp [fingerprint, swap_relabel]

@[simp] theorem fingerprint_swap {n : ℕ} (d : DiagramCode n) :
    fingerprint (swap d) = fingerprint d := by
  simp [fingerprint, min_comm, max_comm]

@[simp] theorem fingerprint_transform {n : ℕ} (d : DiagramCode n)
    (e : Equiv.Perm (Fin n)) (flip : Bool) :
    fingerprint (transform d e flip) = fingerprint d := by
  cases flip <;> simp [transform]

theorem fingerprint_eq_of_mem_orbit {n : ℕ} {d r : DiagramCode n}
    (h : r ∈ orbit d) : fingerprint r = fingerprint d := by
  obtain ⟨e, s, rfl⟩ := (mem_orbit_iff d r).mp h
  exact fingerprint_transform d e s

end CentralConfigurations.DiagramCode
