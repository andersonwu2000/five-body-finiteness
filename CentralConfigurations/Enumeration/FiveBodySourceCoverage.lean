import CentralConfigurations.Enumeration.FiveBodyPairCoverage
import CentralConfigurations.Enumeration.FiveBodyMonochrome
import CentralConfigurations.Enumeration.FiveBodySourceOrbits
import CentralConfigurations.Enumeration.AlgebraicSearch

/-!
# Complete five-body source coverage

The 6,144 single-color inputs and 49,680 surviving relative-labeling inputs
are fully certified. Coarse rejection covers all omitted representative pairs.
Both colors and masses use the same permutation. Appendix I's unique-double-edge
rule removes the two preliminary extra orbits, leaving the twenty source pictures.
-/

namespace CentralConfigurations
open BinaryMatrixCode
open Filter
open scoped Topology
attribute [local irreducible] DiagramCode.orbit FiveBodyMono.representatives
  expandedAppendixMatchedCandidates

theorem FiveBodyPairs.expanded_source_coverage (d : DiagramCode 5)
    (hd : d ∈ expandedAppendixMatchedCandidates FiveBodyMono.representatives) :
    ∃ k : Fin 20, fiveBodySourceDiagram k ∈ DiagramCode.orbit d := by
  unfold expandedAppendixMatchedCandidates at hd
  have hf := Finset.mem_filter.mp hd
  obtain ⟨hfirst,hsecond⟩ := Finset.mem_product.mp hf.1
  obtain ⟨a,ha⟩ := (mem_representatives_iff d.1).mp hfirst
  obtain ⟨⟨bcode,e⟩,hmem,he⟩ := Finset.mem_image.mp hsecond
  obtain ⟨b,hb⟩ := (mem_representatives_iff bcode).mp (Finset.mem_product.mp hmem).1
  have he' : relabel (rep b) e = d.2 := by simpa only [hb] using he
  have hpair : (rep a,relabel (rep b) e) = d := Prod.ext ha he'
  have horder : trace (rep a) ≤ trace (relabel (rep b) e) := by
    simpa only [ha,he'] using hf.2.1
  have hc : appendixCandidateCheck (rep a) (relabel (rep b) e) = true := by
    simpa only [ha,he'] using hf.2.2
  have hcbase : candidateCheck (rep a) (relabel (rep b) e) = true := by
    simp only [appendixCandidateCheck, Bool.and_eq_true] at hc
    exact hc.1
  have hrow := admissible_pair_survives a b e horder ((candidateCheck_eq_true _ _).mp hcbase).2
  obtain ⟨v,hv,hdecode⟩ := permutations_cover e
  obtain ⟨j,hj,hjv⟩ := Array.getElem_of_mem (Array.mem_toList_iff.mp hv)
  let k : Fin 120 := ⟨j,hj⟩
  have hvalue : permutationCodes[k.val]'(by exact k.isLt) = v := hjv
  have hperm : FiveBodyPermutations.decode
      (permutationCodes[k.val]'(by exact k.isLt)) = (e : Fin 5 → Fin 5) :=
    (congrArg FiveBodyPermutations.decode hvalue).trans hdecode
  have hinput : inputPair a b k = d := by
    have hp : inputPair a b k = (rep a,rawRelabel (rep b) e) :=
      congrArg (fun f : Fin 5 → Fin 5 => (rep a,rawRelabel (rep b) f)) hperm
    exact hp.trans (by simpa only [rawRelabel_eq_relabel] using hpair)
  have hcheck : appendixCandidateCheck (inputPair a b k).1 (inputPair a b k).2 = true := by
    simpa only [hinput] using hf.2.2
  simpa only [hinput] using all_rows_covered a b hrow k hcheck

theorem ScaledZWLimit.five_body_source_orbit {mass : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) :
    ∃ k : Fin 20, fiveBodySourceDiagram k ∈ DiagramCode.orbit l.diagramCode := by
  obtain ⟨d,hd,ho⟩ := l.exists_expanded_appendix_candidate hm hb ha hz hw
    FiveBodyMono.representatives FiveBodyMono.monochrome_coverage
  obtain ⟨k,hk⟩ := FiveBodyPairs.expanded_source_coverage d hd
  exact ⟨k,DiagramCode.orbit_transitive ho hk⟩

theorem ScaledZWLimit.five_body_source_orbit_unique {mass : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) :
    ∃! k : Fin 20, fiveBodySourceDiagram k ∈ DiagramCode.orbit l.diagramCode := by
  obtain ⟨k,hk⟩ := l.five_body_source_orbit hm hb ha hz hw
  refine ⟨k,hk,?_⟩
  intro j hj
  exact five_body_source_number_unique hj hk

theorem five_body_source_singular_diagram {mass : Fin 5 → ℝ}
    (q : ℕ → NormalizedSystem ℂ 5 (fun i => (mass i : ℂ))) (hm : ∀ i, 0 < mass i)
    (i j : Fin 5) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hu : ¬ BddAbove (Set.range
      (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖))) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
        atTop (𝓝 0) ∧
      ∃ k : Fin 20, fiveBodySourceDiagram k ∈ DiagramCode.orbit l.leading.diagramCode := by
  obtain ⟨l,hl,_⟩ := extended_rules_of_gauged_unbounded q
    (complex_positive_masses_admissible mass hm) i j hij hg hu
  exact ⟨l,hl,l.leading.five_body_source_orbit hm
    (fun t => (q (l.subsequence t)).toZW.balanced_norms i j hij) hl l.z_nonzero l.w_nonzero⟩

theorem five_body_source_number_of_infinite_gauged (mass : Fin 5 → ℝ)
    (hm : ∀ i, 0 < mass i) (i j : Fin 5) (hij : i ≠ j)
    (hI : {q : NormalizedSystem ℂ 5 (fun a => (mass a : ℂ)) | q.InGauge i j}.Infinite) :
    ∃ q : ℕ → NormalizedSystem ℂ 5 (fun a => (mass a : ℂ)),
      (∀ t, (q t).InGauge i j) ∧
      ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
        Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
          atTop (𝓝 0) ∧
        ∃ k : Fin 20, fiveBodySourceDiagram k ∈ DiagramCode.orbit l.leading.diagramCode := by
  obtain ⟨q,hg,hu⟩ := exists_unbounded_gauged_sequence_of_infinite _ i j hij hI
  obtain ⟨l,hl,hk⟩ := five_body_source_singular_diagram q hm i j hij hg hu
  exact ⟨q,hg,l,hl,hk⟩

end CentralConfigurations
