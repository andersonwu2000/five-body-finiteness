import CentralConfigurations.Enumeration.FourBodyCandidates

/-!
# The five source pictures in Figure 8

Chang (2023), printed p.60, visually cross-checked with the PDF. Body labels
1--4 in the picture correspond to Fin indices 0--3. In this transcription
the first matrix records red strokes/circles and the second records blue;
purple records both. Global color exchange is part of the allowed orbit.
The five masks below are in source order. Their relationship to the enumerated
representatives, and the distinctness of their orbits, are checked separately.
-/

namespace CentralConfigurations

def fourBodySourceRepresentatives : Finset (DiagramCode 4) :=
  ([(366, 366), (352, 352), (352, 1017), (896, 19), (915, 697)].map
    (fun p => (BinaryMatrixCode.fromMask 4 p.1, BinaryMatrixCode.fromMask 4 p.2))).toFinset

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem four_body_source_figures_cover :
    DiagramCode.coverageCheck fourBodyDiagramRepresentatives fourBodySourceRepresentatives = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem four_body_source_figures_return_to_search :
    DiagramCode.coverageCheck fourBodySourceRepresentatives fourBodyMatchedCandidates = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem four_body_source_figures_pass_checks :
    ∀ d ∈ fourBodySourceRepresentatives, candidateCheck d.1 d.2 = true := by
  intro d hd
  simp only [fourBodySourceRepresentatives, List.map_cons, List.map_nil,
    List.toFinset_cons, List.toFinset_nil, Finset.mem_insert, Finset.notMem_empty,
    or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl
  all_goals decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem four_body_source_orbits_distinct :
    ∀ a ∈ fourBodySourceRepresentatives, ∀ b ∈ fourBodySourceRepresentatives,
      b ∈ DiagramCode.orbit a → a = b := by
  decide +kernel

theorem four_body_source_representative_count : fourBodySourceRepresentatives.card = 5 := by decide

open scoped Topology
open Filter

theorem four_body_source_singular_diagram {mass : Fin 4 → ℝ}
    (q : ℕ → NormalizedSystem ℂ 4 (fun i => (mass i : ℂ))) (hm : ∀ i, 0 < mass i)
    (i j : Fin 4) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hu : ¬ BddAbove (Set.range
      (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖))) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
        atTop (𝓝 0) ∧
      ∃ r ∈ fourBodySourceRepresentatives, r ∈ DiagramCode.orbit l.leading.diagramCode := by
  obtain ⟨l, hl, r, hr, ho⟩ := four_body_singular_diagram q hm i j hij hg hu
  obtain ⟨f, hf, hfo⟩ := DiagramCode.coverageCheck_sound four_body_source_figures_cover hr
  exact ⟨l, hl, f, hf, DiagramCode.orbit_transitive ho hfo⟩

end CentralConfigurations
