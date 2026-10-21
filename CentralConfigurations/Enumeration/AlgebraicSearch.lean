import CentralConfigurations.Asymptotics.AlgebraicUnbounded
import CentralConfigurations.Enumeration.OrbitMatching
import CentralConfigurations.Enumeration.FourBodyFigures

/-!
# From infinite gauged solution sets to diagram coverage

Chang's Lemma 2.1 supplies an unbounded sequence, and Lemma 2.2 supplies a
potential bound. The resulting singular limit satisfies the diagram filters.
The coverage theorems take finite candidate certificates as explicit inputs;
FiveBodySourceCoverage.lean provides the five-body instance.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

theorem accepted_candidate_of_infinite_gauged {n : ℕ}
    (mass : Fin n → ℝ) (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j)
    (hI : {q : NormalizedSystem ℂ n (fun k => (mass k : ℂ)) | q.InGauge i j}.Infinite) :
    ∃ q : ℕ → NormalizedSystem ℂ n (fun k => (mass k : ℂ)),
      (∀ t, (q t).InGauge i j) ∧
      ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
        Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
          atTop (𝓝 0) ∧
        ∃ d ∈ acceptedCandidates n, d ∈ DiagramCode.orbit l.leading.diagramCode := by
  obtain ⟨q, hg, hu⟩ := exists_unbounded_gauged_sequence_of_infinite _ i j hij hI
  exact ⟨q, hg, accepted_candidate_of_positive_gauged_unbounded mass q hm i j hij hg hu⟩

theorem expanded_appendix_representative_of_infinite_gauged {n : ℕ}
    (mass : Fin n → ℝ) (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j)
    (hI : {q : NormalizedSystem ℂ n (fun k => (mass k : ℂ)) | q.InGauge i j}.Infinite)
    (monochromeRepresentatives : Finset (BinaryMatrixCode n))
    (hc : monochromeCoverageCheck monochromeRepresentatives = true)
    (diagramRepresentatives : Finset (DiagramCode n))
    (hd : DiagramCode.coverageCheck
      (expandedAppendixMatchedCandidates monochromeRepresentatives) diagramRepresentatives = true) :
    ∃ q : ℕ → NormalizedSystem ℂ n (fun k => (mass k : ℂ)),
      (∀ t, (q t).InGauge i j) ∧
      ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
        Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
          atTop (𝓝 0) ∧
        ∃ r ∈ diagramRepresentatives, r ∈ DiagramCode.orbit l.leading.diagramCode := by
  obtain ⟨q, hg, hu⟩ := exists_unbounded_gauged_sequence_of_infinite _ i j hij hI
  exact ⟨q, hg, expanded_appendix_representative_of_positive_gauged_unbounded
    mass q hm i j hij hg hu monochromeRepresentatives hc diagramRepresentatives hd⟩

/-- In the four-body case the finite coverage certificates are already
checked, so infinitude forces one of the five pictures of Figure 8. -/
theorem four_body_source_diagram_of_infinite_gauged (mass : Fin 4 → ℝ)
    (hm : ∀ i, 0 < mass i) (i j : Fin 4) (hij : i ≠ j)
    (hI : {q : NormalizedSystem ℂ 4 (fun k => (mass k : ℂ)) | q.InGauge i j}.Infinite) :
    ∃ q : ℕ → NormalizedSystem ℂ 4 (fun k => (mass k : ℂ)),
      (∀ t, (q t).InGauge i j) ∧
      ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
        Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
          atTop (𝓝 0) ∧
        ∃ r ∈ fourBodySourceRepresentatives, r ∈ DiagramCode.orbit l.leading.diagramCode := by
  obtain ⟨q, hg, hu⟩ := exists_unbounded_gauged_sequence_of_infinite _ i j hij hI
  exact ⟨q, hg, four_body_source_singular_diagram q hm i j hij hg hu⟩

end CentralConfigurations
