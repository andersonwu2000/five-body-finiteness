import CentralConfigurations.Enumeration.MatchingSearch
import CentralConfigurations.Diagrams.OneCircledStar
import CentralConfigurations.Diagrams.BoundedPotentialRule

/-!
# The two additional Appendix I restrictions

The numerical matrix checks are extended by the one-circled-star test and
Rule 2h's exclusion of a unique double edge. The soundness proof uses a
bounded-potential hypothesis; the actual-sequence entry point obtains it
from the finite-potential-values theorem. Finite coverage certificates are
provided in the enumeration modules.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter Asymptotics

def appendixExtraCheck {n : ℕ} (c d : BinaryMatrixCode n) : Bool :=
  decide (OneCircledStarRule (BinaryMatrixCode.decode c) ∧
    OneCircledStarRule (BinaryMatrixCode.decode d) ∧
    NoSingleDoubleEdgeRule (BinaryMatrixCode.decode c) (BinaryMatrixCode.decode d))

def appendixCandidateCheck {n : ℕ} (c d : BinaryMatrixCode n) : Bool :=
  candidateCheck c d && appendixExtraCheck c d

@[simp] theorem appendixExtraCheck_eq_true {n : ℕ} (c d : BinaryMatrixCode n) :
    appendixExtraCheck c d = true ↔
      OneCircledStarRule (BinaryMatrixCode.decode c) ∧
      OneCircledStarRule (BinaryMatrixCode.decode d) ∧
      NoSingleDoubleEdgeRule (BinaryMatrixCode.decode c) (BinaryMatrixCode.decode d) := by
  simp [appendixExtraCheck]

theorem ZWSystem.unorderedPotential_relabel {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (e : Equiv.Perm (Fin n)) :
    (q.relabel e).toNormalized.unorderedPotential = q.toNormalized.unorderedPotential := by
  rw [← (q.relabel e).toNormalized.potential_eq_unordered,
    ← q.toNormalized.potential_eq_unordered]
  unfold NormalizedSystem.potential
  congr 1
  change (∑ i, ∑ j, if i = j then 0 else
    mass (e i) * mass (e j) * q.delta (e i) (e j)) =
    ∑ i, ∑ j, if i = j then 0 else mass i * mass j * q.delta i j
  calc
    _ = ∑ i, ∑ j, if e i = j then 0 else mass (e i) * mass j * q.delta (e i) j := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [e.injective.eq_iff] using Equiv.sum_comp e
        (fun j => if e i = j then (0 : ℂ) else mass (e i) * mass j * q.delta (e i) j)
    _ = _ := Equiv.sum_comp e
      (fun i => ∑ j, if i = j then (0 : ℂ) else mass i * mass j * q.delta i j)

theorem ScaledZWLimit.appendix_extra_check {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hm : ∀ i, mass i ≠ 0) :
    appendixExtraCheck l.diagramCode.1 l.diagramCode.2 = true := by
  rw [appendixExtraCheck_eq_true]
  simp only [ScaledZWLimit.diagramCode,
    BinaryMatrixCode.decode_encode _ l.z.matrix_binary l.z.matrix_symm,
    BinaryMatrixCode.decode_encode _ l.w.matrix_binary l.w.matrix_symm]
  exact ⟨(l.one_circled_star_rules hb).1, (l.one_circled_star_rules hb).2,
    l.no_single_double_edge_rule hb ha hm⟩

theorem ScaledZWLimit.appendix_diagramCode_check {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) :
    appendixCandidateCheck l.diagramCode.1 l.diagramCode.2 = true := by
  rw [appendixCandidateCheck, Bool.and_eq_true]
  exact ⟨l.diagramCode_check hm hb ha hz hw,
    l.appendix_extra_check hb ha (fun i => Complex.ofReal_ne_zero.mpr (hm i).ne')⟩

theorem ScaledZWLimit.relabel_appendix_diagramCode_check {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) (e : Equiv.Perm (Fin n)) :
    appendixCandidateCheck (DiagramCode.relabel l.diagramCode e).1
      (DiagramCode.relabel l.diagramCode e).2 = true := by
  have hbr : ∀ t, ‖((q t).relabel e).zVector‖ = ‖((q t).relabel e).wVector‖ := by
    simpa only [ZWSystem.zVector_norm_relabel, ZWSystem.wVector_norm_relabel] using hb
  have har : Tendsto (fun t => ((q t).relabel e).inverseScale) atTop (𝓝 0) := by
    simpa only [ZWSystem.inverseScale_relabel] using ha
  have h := (l.relabelCanonical e).appendix_diagramCode_check (fun i => hm (e i)) hbr har
    ((l.z.nonzero_relabel_iff e).mpr hz) ((l.w.nonzero_relabel_iff e).mpr hw)
  simpa only [l.diagramCode_relabelCanonical e] using h

theorem ScaledZWLimit.transform_appendix_diagramCode_check {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) (e : Equiv.Perm (Fin n)) (s : Bool) :
    appendixCandidateCheck (DiagramCode.transform l.diagramCode e s).1
      (DiagramCode.transform l.diagramCode e s).2 = true := by
  cases s
  · exact l.relabel_appendix_diagramCode_check hm hb ha hz hw e
  · have has : Tendsto (fun t => ((q t).swap).inverseScale) atTop (𝓝 0) := by
      change Tendsto (fun t => (‖(q t).wVector‖ : ℂ)⁻¹) atTop (𝓝 0)
      simpa only [ZWSystem.inverseScale, ← hb] using ha
    exact (l.swapBalanced hb).relabel_appendix_diagramCode_check hm
      (fun t => (hb t).symm) has hw hz e

def appendixMatchedCandidates {n : ℕ} (representatives : Finset (BinaryMatrixCode n)) :
    Finset (DiagramCode n) :=
  (matchedCandidates representatives).filter (fun d => appendixExtraCheck d.1 d.2 = true)

theorem ScaledZWLimit.exists_appendix_matched_candidate {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero)
    (representatives : Finset (BinaryMatrixCode n)) (hc : MonochromeCovers representatives) :
    ∃ d ∈ appendixMatchedCandidates representatives, d ∈ DiagramCode.orbit l.diagramCode := by
  obtain ⟨d, hd, ho⟩ := l.exists_matched_candidate hm hb ha hz hw representatives hc
  refine ⟨d, Finset.mem_filter.mpr ⟨hd, ?_⟩, ho⟩
  obtain ⟨e, s, hes⟩ := (DiagramCode.mem_orbit_iff _ _).mp ho
  have h := l.transform_appendix_diagramCode_check hm hb ha hz hw e s
  rw [hes, appendixCandidateCheck, Bool.and_eq_true] at h
  exact h.2

/-- Lemma 2.2 supplies the potential bound internally. The input is an
unbounded gauged sequence; finite search coverage remains an explicit certificate. -/
theorem appendix_representative_of_positive_gauged_unbounded {n : ℕ} (mass : Fin n → ℝ)
    (q : ℕ → NormalizedSystem ℂ n (fun i => (mass i : ℂ))) (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hu : ¬ BddAbove (Set.range
      (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖)))
    (monochromeRepresentatives : Finset (BinaryMatrixCode n))
    (hc : monochromeCoverageCheck monochromeRepresentatives = true)
    (diagramRepresentatives : Finset (DiagramCode n))
    (hd : DiagramCode.coverageCheck (appendixMatchedCandidates monochromeRepresentatives)
      diagramRepresentatives = true) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
        atTop (𝓝 0) ∧
      ∃ r ∈ diagramRepresentatives, r ∈ DiagramCode.orbit l.leading.diagramCode := by
  obtain ⟨l, hl, _⟩ := extended_rules_of_gauged_unbounded q
    (complex_positive_masses_admissible mass hm) i j hij hg hu
  obtain ⟨d, hdm, hdo⟩ := l.leading.exists_appendix_matched_candidate hm
    (fun t => (q (l.subsequence t)).toZW.balanced_norms i j hij) hl l.z_nonzero l.w_nonzero
    monochromeRepresentatives (monochromeCoverageCheck_sound hc)
  obtain ⟨r, hr, hro⟩ := DiagramCode.coverageCheck_sound hd hdm
  exact ⟨l, hl, r, hr, DiagramCode.orbit_transitive hdo hro⟩

end CentralConfigurations
