import CentralConfigurations.Enumeration.AppendixSearch

/-!
# A proved second-color orbit expansion

The second matrix keeps every labeling of each monochrome representative.
It is never independently replaced by a representative in the final diagram.
For an actual singular diagram, sorting the second diagonal and applying the
monochrome coverage theorem proves that its original labeling lies in this
expanded set. Thus the raw second-color space of 2^(n(n+1)/2) binary matrices
can be replaced by the usually much smaller orbit expansion.

This argument reapplies necessary conditions to actual relabeled solutions;
it does not assume invariance of the appendix's order-dependent group test.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

def monochromeOrbitExpansion {n : ℕ} (representatives : Finset (BinaryMatrixCode n)) :
    Finset (BinaryMatrixCode n) :=
  (representatives.product Finset.univ).image
    (fun p : BinaryMatrixCode n × Equiv.Perm (Fin n) => BinaryMatrixCode.relabel p.1 p.2)

theorem ScaledZWLimit.orbit_second_mem_expansion {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero)
    (representatives : Finset (BinaryMatrixCode n)) (hc : MonochromeCovers representatives)
    (d : DiagramCode n) (hd : d ∈ DiagramCode.orbit l.diagramCode) :
    d.2 ∈ monochromeOrbitExpansion representatives := by
  let f := BinaryMatrixCode.sortDiagonal d.2
  have hv : DiagramCode.relabel d f ∈ DiagramCode.orbit l.diagramCode :=
    DiagramCode.orbit_transitive hd ((DiagramCode.mem_orbit_iff _ _).mpr ⟨f, false, rfl⟩)
  have hvcheck : candidateCheck (DiagramCode.relabel d f).1
      (DiagramCode.relabel d f).2 = true := by
    obtain ⟨g, s, hgs⟩ := (DiagramCode.mem_orbit_iff _ _).mp hv
    rw [← hgs]
    exact l.transform_diagramCode_check hm hb ha hz hw g s
  have hmono : BinaryMatrixCode.relabel d.2 f ∈ monochromeCandidates n := by
    apply Finset.mem_filter.mpr
    exact ⟨BinaryMatrixCode.normalized_mem_prefixCandidates d.2,
      (monochromeCheck_eq_true _).mpr ((candidateCheck_eq_true _ _).mp hvcheck).1.2⟩
  obtain ⟨r, hr, e, he⟩ := hc _ hmono
  rw [BinaryMatrixCode.relabel_relabel] at he
  have hback : BinaryMatrixCode.relabel r (e.trans f).symm = d.2 := by
    rw [← he, BinaryMatrixCode.relabel_inverse]
  exact Finset.mem_image.mpr ⟨(r, (e.trans f).symm),
    Finset.mem_product.mpr ⟨hr, Finset.mem_univ _⟩, hback⟩

def expandedAppendixMatchedCandidates {n : ℕ}
    (representatives : Finset (BinaryMatrixCode n)) : Finset (DiagramCode n) :=
  (representatives.product (monochromeOrbitExpansion representatives)).filter
    (fun d => BinaryMatrixCode.trace d.1 ≤ BinaryMatrixCode.trace d.2 ∧
      appendixCandidateCheck d.1 d.2 = true)

theorem ScaledZWLimit.exists_expanded_appendix_candidate {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero)
    (representatives : Finset (BinaryMatrixCode n)) (hc : MonochromeCovers representatives) :
    ∃ d ∈ expandedAppendixMatchedCandidates representatives,
      d ∈ DiagramCode.orbit l.diagramCode := by
  obtain ⟨d, hd, ho⟩ := l.exists_matched_candidate hm hb ha hz hw representatives hc
  have hs := l.orbit_second_mem_expansion hm hb ha hz hw representatives hc d ho
  have hf := Finset.mem_filter.mp hd
  have hp := Finset.mem_product.mp hf.1
  refine ⟨d, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp.1, hs⟩, hf.2.1, ?_⟩, ho⟩
  obtain ⟨e, s, hes⟩ := (DiagramCode.mem_orbit_iff _ _).mp ho
  rw [← hes]
  exact l.transform_appendix_diagramCode_check hm hb ha hz hw e s

theorem expanded_appendix_representative_of_positive_gauged_unbounded {n : ℕ}
    (mass : Fin n → ℝ) (q : ℕ → NormalizedSystem ℂ n (fun i => (mass i : ℂ)))
    (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hu : ¬ BddAbove (Set.range
      (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖)))
    (monochromeRepresentatives : Finset (BinaryMatrixCode n))
    (hc : monochromeCoverageCheck monochromeRepresentatives = true)
    (diagramRepresentatives : Finset (DiagramCode n))
    (hd : DiagramCode.coverageCheck
      (expandedAppendixMatchedCandidates monochromeRepresentatives) diagramRepresentatives = true) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
        atTop (𝓝 0) ∧
      ∃ r ∈ diagramRepresentatives, r ∈ DiagramCode.orbit l.leading.diagramCode := by
  obtain ⟨l, hl, _⟩ := extended_rules_of_gauged_unbounded q
    (complex_positive_masses_admissible mass hm) i j hij hg hu
  obtain ⟨d, hdm, hdo⟩ := l.leading.exists_expanded_appendix_candidate hm
    (fun t => (q (l.subsequence t)).toZW.balanced_norms i j hij) hl l.z_nonzero l.w_nonzero
    monochromeRepresentatives (monochromeCoverageCheck_sound hc)
  obtain ⟨r, hr, hro⟩ := DiagramCode.coverageCheck_sound hd hdm
  exact ⟨l, hl, r, hr, DiagramCode.orbit_transitive hdo hro⟩

end CentralConfigurations
