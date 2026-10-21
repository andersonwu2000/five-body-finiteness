import CentralConfigurations.Enumeration.FiveBodySourceCoverage
import CentralConfigurations.Enumeration.FiveBodyOrderTree9
import CentralConfigurations.Enumeration.FiveBodyOrderTree11
import CentralConfigurations.Enumeration.FiveBodyOrderTree13
import CentralConfigurations.Enumeration.FiveBodyOrderTree17
import CentralConfigurations.Enumeration.OrderedDiagramRealization
import CentralConfigurations.Model.PhysicalSimilarity

/-!
# Section 10: the sixteen surviving five-body source diagrams

All twenty source pictures cover actual singular limits. The four exclusions
are exact refutation trees of the already proved order rules, with every branch
covered. Physical infinitude reaches an actual realization on the original
source labels, with the same permutation applied to the masses.
-/

namespace CentralConfigurations
open Filter
open scoped Topology
attribute [local irreducible] DiagramCode.orbit

def fiveBodyOrderExclusions : Finset (Fin 20) := {8,10,12,16}
def fiveBodyOrderSurvivors : Finset (Fin 20) := Finset.univ \ fiveBodyOrderExclusions
def fiveBodySixteenRepresentatives : Finset (DiagramCode 5) :=
  fiveBodyOrderSurvivors.image fiveBodySourceDiagram

theorem five_body_order_exclusion_count : fiveBodyOrderExclusions.card = 4 := by decide +kernel
theorem five_body_order_survivor_count : fiveBodyOrderSurvivors.card = 16 := by decide +kernel
theorem five_body_sixteen_representative_count : fiveBodySixteenRepresentatives.card = 16 := by
  rw [fiveBodySixteenRepresentatives,
    Finset.card_image_of_injective _ five_body_source_diagram_injective]
  exact five_body_order_survivor_count

theorem OrderedDiagramRealization.five_body_source_index_survives {mass : Fin 5 → ℂ}
    {k : Fin 20} (r : OrderedDiagramRealization mass (fiveBodySourceDiagram k))
    (hm : AdmissibleMasses mass) : k ∈ fiveBodyOrderSurvivors := by
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  intro hk
  have hc : k=8 ∨ k=10 ∨ k=12 ∨ k=16 := by
    simpa only [fiveBodyOrderExclusions,Finset.mem_insert,Finset.mem_singleton] using hk
  rcases hc with rfl | rfl | rfl | rfl
  · exact FiveBodyOrderTreeCertificates.diagram9_impossible r.sequence r.anchor₁ r.anchor₂
      r.anchors_distinct r.vanishing r.balanced r.leading hm r.diagram_eq
  · exact FiveBodyOrderTreeCertificates.diagram11_impossible r.sequence r.anchor₁ r.anchor₂
      r.anchors_distinct r.vanishing r.balanced r.leading hm r.diagram_eq
  · exact FiveBodyOrderTreeCertificates.diagram13_impossible r.sequence r.anchor₁ r.anchor₂
      r.anchors_distinct r.vanishing r.balanced r.leading hm r.diagram_eq
  · exact FiveBodyOrderTreeCertificates.diagram17_impossible r.sequence r.anchor₁ r.anchor₂
      r.anchors_distinct r.vanishing r.balanced r.leading hm r.diagram_eq

theorem ScaledZWLimit.five_body_surviving_source_realization {mass : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ a, 0 < mass a)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j : Fin 5) (hij : i ≠ j)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) :
    ∃ k ∈ fiveBodyOrderSurvivors,
      fiveBodySourceDiagram k ∈ DiagramCode.orbit l.diagramCode ∧
      ∃ e : Equiv.Perm (Fin 5), (∀ a, 0 < mass (e a)) ∧
        Nonempty (OrderedDiagramRealization (fun a => (mass (e a) : ℂ)) (fiveBodySourceDiagram k)) := by
  obtain ⟨k,hk⟩ := l.five_body_source_orbit hm hb ha hz hw
  obtain ⟨e,⟨r⟩⟩ := ordered_realization_of_mem_orbit q hb i j hij ha l hz hw hk
  have hp : ∀ a, 0 < mass (e a) := fun a => hm (e a)
  exact ⟨k,r.five_body_source_index_survives (complex_positive_masses_admissible _ hp),
    hk,e,hp,⟨r⟩⟩

theorem five_body_sixteen_realization_of_infinite_gauged (mass : Fin 5 → ℝ)
    (hm : ∀ a, 0 < mass a) (i j : Fin 5) (hij : i ≠ j)
    (hI : {q : NormalizedSystem ℂ 5 (fun a => (mass a : ℂ)) | q.InGauge i j}.Infinite) :
    ∃ k ∈ fiveBodyOrderSurvivors, ∃ e : Equiv.Perm (Fin 5),
      (∀ a, 0 < mass (e a)) ∧
      Nonempty (OrderedDiagramRealization (fun a => (mass (e a) : ℂ)) (fiveBodySourceDiagram k)) := by
  obtain ⟨q,hg,hu⟩ := exists_unbounded_gauged_sequence_of_infinite _ i j hij hI
  obtain ⟨l,hl,_⟩ := extended_rules_of_gauged_unbounded q
    (complex_positive_masses_admissible mass hm) i j hij hg hu
  obtain ⟨k,hk,_,e,hp,hr⟩ := l.leading.five_body_surviving_source_realization hm
    (fun t => (q (l.subsequence t)).toZW.balanced_norms i j hij) i j hij hl l.z_nonzero l.w_nonzero
  exact ⟨k,hk,e,hp,hr⟩

theorem five_body_sixteen_realization_of_infinite_physical_classes (mass : Fin 5 → ℝ)
    (hm : ∀ a, 0 < mass a) (i j : Fin 5) (hij : i ≠ j)
    [Infinite (PhysicalSimilarityClass 5 mass)] :
    ∃ k ∈ fiveBodyOrderSurvivors, ∃ e : Equiv.Perm (Fin 5),
      (∀ a, 0 < mass (e a)) ∧
      Nonempty (OrderedDiagramRealization (fun a => (mass (e a) : ℂ)) (fiveBodySourceDiagram k)) :=
  five_body_sixteen_realization_of_infinite_gauged mass hm i j hij
    (infinite_gauged_of_infinite_physical_classes mass hm i j hij)

end CentralConfigurations
