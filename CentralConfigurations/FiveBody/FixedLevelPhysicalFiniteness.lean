import CentralConfigurations.FiveBody.FixedLevelFiniteness
import CentralConfigurations.FiveBody.PhysicalPotentialFloor
import CentralConfigurations.Model.PhysicalSimilarity

/-!
# Physical classes from finite fibers at physical potential levels

The real representative retains the positive inverse-distance branch.
Its potential value determines the surrounding complex affine fiber.
The finiteness theorem takes the local four-product decay statement as an
explicit premise. ClassifiedPhysicalFiniteness.lean and
D2Regular/PositiveFiniteness.lean discharge it for five positive masses.
-/

namespace CentralConfigurations
noncomputable section

namespace PhysicalCentralConfiguration

theorem exists_gauged_similar_positive {n : ℕ} {mass : Fin n → ℝ}
    (q : PhysicalCentralConfiguration n mass) (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ p : NormalizedSystem ℝ n mass, p.InGauge i j ∧
      PlanarSimilar (q.x, q.y) (p.x, p.y) ∧
      (∀ a b, a ≠ b → 0 < p.delta a b) := by
  obtain ⟨s, a, b, p, hs, _, hab, hg, _, hx, hy, _, hdelta⟩ :=
    q.exists_gauged_normalization hm i j hij
  refine ⟨p, hg, ?_, hdelta⟩
  refine ⟨s, a, b, -s * (a * q.centerX + b * q.centerY),
    -s * (-b * q.centerX + a * q.centerY), hs, hab, ?_, ?_⟩
  · intro k; dsimp only; rw [hx k]; ring
  · intro k; dsimp only; rw [hy k]; ring

def positiveGaugeRepresentative {n : ℕ} {mass : Fin n → ℝ}
    (q : PhysicalCentralConfiguration n mass) (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j) : NormalizedSystem ℝ n mass :=
  Classical.choose (q.exists_gauged_similar_positive hm i j hij)

theorem positiveGaugeRepresentative_spec {n : ℕ} {mass : Fin n → ℝ}
    (q : PhysicalCentralConfiguration n mass) (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j) :
    (q.positiveGaugeRepresentative hm i j hij).InGauge i j ∧
      PlanarSimilar (q.x, q.y)
        ((q.positiveGaugeRepresentative hm i j hij).x,
          (q.positiveGaugeRepresentative hm i j hij).y) ∧
      (∀ a b, a ≠ b → 0 < (q.positiveGaugeRepresentative hm i j hij).delta a b) :=
  Classical.choose_spec (q.exists_gauged_similar_positive hm i j hij)

end PhysicalCentralConfiguration

def physicalPotentialValues (mass : Fin 5 → ℝ) : Set ℂ :=
  {z | ∃ c : ℝ, PhysicalPotentialLevel mass c ∧ z = (c : ℂ)}

def physicalClassToPotentialGauge {mass : Fin 5 → ℝ}
    (hm : ∀ i, 0 < mass i) (i j : Fin 5) (hij : i ≠ j)
    (c : PhysicalSimilarityClass 5 mass) :
    {q : NormalizedSystem ℂ 5 (fun k => (mass k : ℂ)) //
      q.InGauge i j ∧ q.unorderedPotential ∈ physicalPotentialValues mass} := by
  let p := c.out.positiveGaugeRepresentative hm i j hij
  have hp := c.out.positiveGaugeRepresentative_spec hm i j hij
  refine ⟨p.map Complex.ofRealHom,
    NormalizedSystem.map_inGauge _ _ hp.1, p.unorderedPotential,
      p.physicalPotentialLevel hm hp.2.2, ?_⟩
  exact p.map_unorderedPotential Complex.ofRealHom

theorem physicalClassToPotentialGauge_injective {mass : Fin 5 → ℝ}
    (hm : ∀ i, 0 < mass i) (i j : Fin 5) (hij : i ≠ j) :
    Function.Injective (physicalClassToPotentialGauge hm i j hij) := by
  intro c d he
  let p := c.out.positiveGaugeRepresentative hm i j hij
  let q := d.out.positiveGaugeRepresentative hm i j hij
  have hxy : (p.x, p.y) = (q.x, q.y) := by
    apply Prod.ext
    · funext k
      exact Complex.ofReal_injective (congrArg (fun z => z.val.x k) he)
    · funext k
      exact Complex.ofReal_injective (congrArg (fun z => z.val.y k) he)
  have hp : PlanarSimilar (c.out.x, c.out.y) (p.x, p.y) :=
    (c.out.positiveGaugeRepresentative_spec hm i j hij).2.1
  have hq : PlanarSimilar (d.out.x, d.out.y) (q.x, q.y) :=
    (d.out.positiveGaugeRepresentative_spec hm i j hij).2.1
  rw [hxy] at hp
  exact Quotient.out_equiv_out.mp (hp.trans hq.symm)

/-- Conditional physical finiteness endpoint. Every analytic exclusion and
the complete D5 product bound must supply `hdecay` for each physical scalar.
The same mass-dependent positive product R is used at both selections. -/
theorem finite_physical_classes_of_fixed_level_decay (mass : Fin 5 → ℝ)
    (hm : ∀ i, 0 < mass i) (i j : Fin 5) (hij : i ≠ j) (R : Finset (Fin 10))
    (hdecay : ∀ c : ℝ, PhysicalPotentialLevel mass c →
      FixedLevelFourProductDecay (fun k => (mass k : ℂ)) i j (c : ℂ) R) :
    Finite (PhysicalSimilarityClass 5 mass) := by
  have hlevels : ∀ c ∈ physicalPotentialValues mass,
      (fixedPotentialGauge (fun k => (mass k : ℂ)) i j c).Finite := by
    rintro _ ⟨c, hc, rfl⟩
    exact finite_fixedPotentialGauge_of_four_product_decay _ i j hij _ R (hdecay c hc)
  have hfinite := finite_gauge_on_selected_potential_values
    (fun k => (mass k : ℂ)) i j (physicalPotentialValues mass) hlevels
  letI : Finite {q : NormalizedSystem ℂ 5 (fun k => (mass k : ℂ)) //
      q.InGauge i j ∧ q.unorderedPotential ∈ physicalPotentialValues mass} :=
    Set.finite_coe_iff.mpr hfinite
  exact Finite.of_injective _ (physicalClassToPotentialGauge_injective hm i j hij)

end
end CentralConfigurations
