import CentralConfigurations.Enumeration.MatrixFilters
import CentralConfigurations.Enumeration.DiagramOrbits
import CentralConfigurations.Asymptotics.Relabeling

/-!
# Coverage of actual singular diagrams by the normalized search

Every positive-mass balanced singular limit has an accepted representative
whose first diagonal is sorted and whose traces are ordered. Relabeling is
performed on actual solutions, with masses transported by the same permutation.
Thus no relabeling-invariance assumption is imposed on the appendix's greedy
component extraction. A concrete exhaustive representative certificate remains
separate from this general coverage proof.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

noncomputable def ScaledZWLimit.diagramCode {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a) : DiagramCode n :=
  (BinaryMatrixCode.encode l.z.matrix, BinaryMatrixCode.encode l.w.matrix)

theorem ScaledZWLimit.diagramCode_relabelCanonical {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (e : Equiv.Perm (Fin n)) :
    (l.relabelCanonical e).diagramCode = DiagramCode.relabel l.diagramCode e := by
  change (BinaryMatrixCode.encode (l.z.relabel e).matrix,
    BinaryMatrixCode.encode (l.w.relabel e).matrix) =
    (BinaryMatrixCode.relabel (BinaryMatrixCode.encode l.z.matrix) e,
      BinaryMatrixCode.relabel (BinaryMatrixCode.encode l.w.matrix) e)
  simp only [BinaryMatrixCode.relabel, OneColorLimit.matrix_relabel,
    BinaryMatrixCode.decode_encode _ l.z.matrix_binary l.z.matrix_symm,
    BinaryMatrixCode.decode_encode _ l.w.matrix_binary l.w.matrix_symm]

theorem ScaledZWLimit.diagramCode_check {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) :
    candidateCheck l.diagramCode.1 l.diagramCode.2 = true :=
  (l.extendedMatrixRules hb ha (complex_positive_masses_admissible mass hm) hz hw).candidate_check hm

theorem ScaledZWLimit.relabel_diagramCode_check {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) (e : Equiv.Perm (Fin n)) :
    candidateCheck (DiagramCode.relabel l.diagramCode e).1
      (DiagramCode.relabel l.diagramCode e).2 = true := by
  have hbr : ∀ t, ‖((q t).relabel e).zVector‖ = ‖((q t).relabel e).wVector‖ := by
    simpa only [ZWSystem.zVector_norm_relabel, ZWSystem.wVector_norm_relabel] using hb
  have har : Tendsto (fun t => ((q t).relabel e).inverseScale) atTop (𝓝 0) := by
    simpa only [ZWSystem.inverseScale_relabel] using ha
  have h := (l.relabelCanonical e).diagramCode_check (fun i => hm (e i)) hbr har
    ((l.z.nonzero_relabel_iff e).mpr hz) ((l.w.nonzero_relabel_iff e).mpr hw)
  simpa only [l.diagramCode_relabelCanonical e] using h

theorem ScaledZWLimit.transform_diagramCode_check {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) (e : Equiv.Perm (Fin n)) (s : Bool) :
    candidateCheck (DiagramCode.transform l.diagramCode e s).1
      (DiagramCode.transform l.diagramCode e s).2 = true := by
  cases s
  · exact l.relabel_diagramCode_check hm hb ha hz hw e
  · have has : Tendsto (fun t => ((q t).swap).inverseScale) atTop (𝓝 0) := by
      change Tendsto (fun t => (‖(q t).wVector‖ : ℂ)⁻¹) atTop (𝓝 0)
      simpa only [ZWSystem.inverseScale, ← hb] using ha
    exact (l.swapBalanced hb).relabel_diagramCode_check hm (fun t => (hb t).symm) has hw hz e

/-- Reference search space, not an optimized implementation or certified count. -/
def acceptedCandidates (n : ℕ) : Finset (DiagramCode n) :=
  (DiagramCode.normalizedCandidates n).filter (fun d => candidateCheck d.1 d.2 = true)

theorem ScaledZWLimit.normalize_mem_accepted {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) :
    DiagramCode.normalize l.diagramCode ∈ acceptedCandidates n := by
  apply Finset.mem_filter.mpr
  refine ⟨DiagramCode.normalize_mem_candidates l.diagramCode, ?_⟩
  obtain ⟨e, s, he⟩ := (DiagramCode.mem_orbit_iff _ _).mp
    (DiagramCode.normalize_mem_orbit l.diagramCode)
  rw [← he]
  exact l.transform_diagramCode_check hm hb ha hz hw e s

/-- The same extracted sequence supplies an accepted normalized orbit
representative. `AlgebraicSearch.lean` supplies the proved algebraic-geometric
bridge when the input is infinitely many gauged configurations. -/
theorem accepted_candidate_of_positive_gauged_unbounded {n : ℕ} (mass : Fin n → ℝ)
    (q : ℕ → NormalizedSystem ℂ n (fun i => (mass i : ℂ))) (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hu : ¬ BddAbove (Set.range
      (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖))) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
        atTop (𝓝 0) ∧
      ∃ d ∈ acceptedCandidates n, d ∈ DiagramCode.orbit l.leading.diagramCode := by
  obtain ⟨l, hl, _⟩ := extended_rules_of_gauged_unbounded q
    (complex_positive_masses_admissible mass hm) i j hij hg hu
  exact ⟨l, hl, DiagramCode.normalize l.leading.diagramCode,
    l.leading.normalize_mem_accepted hm
      (fun t => (q (l.subsequence t)).toZW.balanced_norms i j hij) hl l.z_nonzero l.w_nonzero,
    DiagramCode.normalize_mem_orbit l.leading.diagramCode⟩

/-- A checked representative list completes this part of Algorithm I's
coverage obligation. No particular list is asserted to pass the checker. -/
theorem representative_of_positive_gauged_unbounded {n : ℕ} (mass : Fin n → ℝ)
    (q : ℕ → NormalizedSystem ℂ n (fun i => (mass i : ℂ))) (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hu : ¬ BddAbove (Set.range
      (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖)))
    (representatives : Finset (DiagramCode n))
    (hc : DiagramCode.coverageCheck (acceptedCandidates n) representatives = true) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
        atTop (𝓝 0) ∧
      ∃ r ∈ representatives, r ∈ DiagramCode.orbit l.leading.diagramCode := by
  obtain ⟨l, hl, d, hd, ho⟩ :=
    accepted_candidate_of_positive_gauged_unbounded mass q hm i j hij hg hu
  obtain ⟨r, hr, hro⟩ := DiagramCode.coverageCheck_sound hc hd
  exact ⟨l, hl, r, hr, DiagramCode.orbit_transitive ho hro⟩

end CentralConfigurations
