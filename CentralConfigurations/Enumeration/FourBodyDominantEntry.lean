import CentralConfigurations.Asymptotics.DominantDistances
import CentralConfigurations.Enumeration.FourBodyFigures
import CentralConfigurations.Model.PhysicalSimilarity
import CentralConfigurations.Diagrams.ComponentMassRelations

/-!
# Section 9.1: choose a singular limit outside the fully edged orbit

Infinitely many gauged solutions yield a sequence with one diverging
squared distance. Reciprocal balancing preserves the inverse distances,
and strict subsequences preserve divergence. A double edge would instead
make that distance tend to zero. Hence the selected four-body singular
limit belongs to one of source Figures 8.2--8.5.

This is an existential choice of singular limit, not exclusion of every
fully edged singular limit. The FourBody modules supply mass restrictions
for the selected diagrams.
-/

namespace CentralConfigurations
noncomputable section
open scoped Topology
open Filter Asymptotics

theorem NormalizedSystem.inverse_distance_squared {n : ℕ} {mass : Fin n → ℂ}
    (q : NormalizedSystem ℂ n mass) {a b : Fin n} (hab : a ≠ b) :
    (q.delta a b)⁻¹ ^ 2 = squaredSeparation q.x q.y a b := by
  apply mul_left_cancel₀ (pow_ne_zero 2 (q.delta_ne_zero hab))
  rw [← mul_pow, mul_inv_cancel₀ (q.delta_ne_zero hab), one_pow, q.distance a b hab]

theorem ScaledZWLimit.double_edge_radius_tendsto_zero {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (a b : Fin n) (hab : a ≠ b)
    (hz : l.z.force a b ≠ 0) (hw : l.w.force a b ≠ 0) :
    Tendsto (fun t => ((q t).delta a b)⁻¹) atTop (𝓝 0) := by
  let p := ZWSystem.pairEstimateData q hb a b hab
  have hr := p.double_force_iff_radius.mp
    ⟨(l.pair_z_stroke_iff hb a b hab).mpr hz, (l.pair_w_stroke_iff hb a b hab).mpr hw⟩
  exact hr.tendsto_zero_iff.mpr (ZWSystem.epsilon_tendsto_zero_of_inverseScale q ha)

def fourBodyFullyEdgedSource : DiagramCode 4 :=
  (BinaryMatrixCode.fromMask 4 366, BinaryMatrixCode.fromMask 4 366)

def fourBodyNoncompleteSourceRepresentatives : Finset (DiagramCode 4) :=
  fourBodySourceRepresentatives.erase fourBodyFullyEdgedSource

theorem four_body_noncomplete_source_count :
    fourBodyNoncompleteSourceRepresentatives.card = 4 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem four_body_fully_edged_orbit_has_all_strokes :
    ∀ d ∈ DiagramCode.orbit fourBodyFullyEdgedSource,
      ∀ a b : Fin 4, a ≠ b →
        d.1 (upperIndex a b) = true ∧ d.2 (upperIndex a b) = true := by decide +kernel

theorem four_body_noncomplete_source_of_infinite_gauged (mass : Fin 4 → ℝ)
    (hm : ∀ a, 0 < mass a) (i j : Fin 4) (hij : i ≠ j)
    (hI : {q : NormalizedSystem ℂ 4 (fun k => (mass k : ℂ)) | q.InGauge i j}.Infinite) :
    ∃ a b : Fin 4, a ≠ b ∧
      ∃ q : ℕ → NormalizedSystem ℂ 4 (fun k => (mass k : ℂ)),
        (∀ t, (q t).InGauge i j) ∧
        Tendsto (fun t => ‖squaredSeparation (q t).x (q t).y a b‖) atTop atTop ∧
        ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
          Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
            atTop (𝓝 0) ∧
          ∃ r ∈ fourBodyNoncompleteSourceRepresentatives,
            r ∈ DiagramCode.orbit l.leading.diagramCode := by
  obtain ⟨a, b, hab, q, hg, hd, hu⟩ :=
    exists_escaping_distance_sequence_of_infinite_gauged _ i j hij hI
  obtain ⟨l, ha, r, hr, ho⟩ := four_body_source_singular_diagram q hm i j hij hg hu
  refine ⟨a, b, hab, q, hg, hd, l, ha, r, Finset.mem_erase.mpr ⟨?_, hr⟩, ho⟩
  intro he
  have hfull := four_body_fully_edged_orbit_has_all_strokes l.leading.diagramCode
    (DiagramCode.orbit_symmetric (he ▸ ho)) a b hab
  have hz := l.leading.z_force_ne_zero_of_code rfl a b hab hfull.1
  have hw := l.leading.w_force_ne_zero_of_code rfl a b hab hfull.2
  have hzero := l.leading.double_edge_radius_tendsto_zero
    (fun t => (q (l.subsequence t)).toZW.balanced_norms i j hij) ha a b hab hz hw
  have hsq := hzero.pow 2
  change Tendsto (fun t => ((q (l.subsequence t)).delta a b)⁻¹ ^ 2) atTop
    (𝓝 ((0 : ℂ) ^ 2)) at hsq
  simp only [NormalizedSystem.inverse_distance_squared _ hab, zero_pow (by decide : 2 ≠ 0)] at hsq
  have hn := hsq.norm
  simp only [norm_zero] at hn
  exact not_tendsto_atTop_of_tendsto_nhds hn (hd.comp l.strictMono.tendsto_atTop)

theorem four_body_noncomplete_source_of_infinite_physical_classes (mass : Fin 4 → ℝ)
    (hm : ∀ a, 0 < mass a) (i j : Fin 4) (hij : i ≠ j)
    [Infinite (PhysicalSimilarityClass 4 mass)] :
    ∃ a b : Fin 4, a ≠ b ∧
      ∃ q : ℕ → NormalizedSystem ℂ 4 (fun k => (mass k : ℂ)),
        (∀ t, (q t).InGauge i j) ∧
        Tendsto (fun t => ‖squaredSeparation (q t).x (q t).y a b‖) atTop atTop ∧
        ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
          Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
            atTop (𝓝 0) ∧
          ∃ r ∈ fourBodyNoncompleteSourceRepresentatives,
            r ∈ DiagramCode.orbit l.leading.diagramCode :=
  four_body_noncomplete_source_of_infinite_gauged mass hm i j hij
    (infinite_gauged_of_infinite_physical_classes mass hm i j hij)

end
end CentralConfigurations
