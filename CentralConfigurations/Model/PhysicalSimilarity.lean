import CentralConfigurations.Model.PhysicalCoordinates
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Quot

/-!
# Physical similarity classes and the fixed-gauge algebraic solution set

Proper similarities are translations, positive scales, and planar rotations.
Using this finer equivalence (without reflections or relabeling) suffices for
finiteness modulo any of those additional identifications as well.
-/

namespace CentralConfigurations

abbrev PlanarPoints (n : ℕ) := (Fin n → ℝ) × (Fin n → ℝ)

def PlanarSimilar {n : ℕ} (p q : PlanarPoints n) : Prop :=
  ∃ s a b tx ty : ℝ, 0 < s ∧ a ^ 2 + b ^ 2 = 1 ∧
    (∀ k, q.1 k = s * (a * p.1 k + b * p.2 k) + tx) ∧
    (∀ k, q.2 k = s * (-b * p.1 k + a * p.2 k) + ty)

theorem PlanarSimilar.refl {n : ℕ} (p : PlanarPoints n) : PlanarSimilar p p := by
  refine ⟨1, 1, 0, 0, 0, by norm_num, by norm_num, ?_, ?_⟩ <;> intro k <;> ring

theorem PlanarSimilar.symm {n : ℕ} {p q : PlanarPoints n}
    (h : PlanarSimilar p q) : PlanarSimilar q p := by
  obtain ⟨s, a, b, tx, ty, hs, hab, hx, hy⟩ := h
  have hs0 : s ≠ 0 := ne_of_gt hs
  refine ⟨s⁻¹, a, -b, -(a * tx - b * ty) / s, -(b * tx + a * ty) / s,
    inv_pos.mpr hs, by nlinarith [hab], ?_, ?_⟩
  · intro k
    rw [hx k, hy k]
    field_simp
    linear_combination -(p.1 k * s) * hab
  · intro k
    rw [hx k, hy k]
    field_simp
    linear_combination -(p.2 k * s) * hab

theorem PlanarSimilar.trans {n : ℕ} {p q r : PlanarPoints n}
    (h : PlanarSimilar p q) (h' : PlanarSimilar q r) : PlanarSimilar p r := by
  obtain ⟨s, a, b, tx, ty, hs, hab, hx, hy⟩ := h
  obtain ⟨u, c, d, vx, vy, hu, hcd, hx', hy'⟩ := h'
  have ht : (c * a - d * b) ^ 2 + (c * b + d * a) ^ 2 = 1 := by
    calc
      _ = (c ^ 2 + d ^ 2) * (a ^ 2 + b ^ 2) := by ring
      _ = 1 := by rw [hab, hcd]; norm_num
  refine ⟨u * s, c * a - d * b, c * b + d * a,
    u * (c * tx + d * ty) + vx, u * (-d * tx + c * ty) + vy,
    mul_pos hu hs, ht, ?_, ?_⟩
  · intro k; rw [hx' k, hx k, hy k]; ring
  · intro k; rw [hy' k, hx k, hy k]; ring

def physicalSimilaritySetoid (n : ℕ) (mass : Fin n → ℝ) :
    Setoid (PhysicalCentralConfiguration n mass) where
  r p q := PlanarSimilar (p.x, p.y) (q.x, q.y)
  iseqv := ⟨fun _ => PlanarSimilar.refl _, fun h => h.symm, fun h h' => h.trans h'⟩

abbrev PhysicalSimilarityClass (n : ℕ) (mass : Fin n → ℝ) :=
  Quotient (physicalSimilaritySetoid n mass)

namespace PhysicalCentralConfiguration

variable {n : ℕ} {mass : Fin n → ℝ}

theorem exists_gauged_similar (q : PhysicalCentralConfiguration n mass)
    (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j) :
    ∃ p : NormalizedSystem ℝ n mass, p.InGauge i j ∧ PlanarSimilar (q.x, q.y) (p.x, p.y) := by
  obtain ⟨s, a, b, p, hs, _, hab, hg, _, hx, hy, _, _⟩ :=
    q.exists_gauged_normalization hm i j hij
  refine ⟨p, hg, s, a, b, -s * (a * q.centerX + b * q.centerY),
    -s * (-b * q.centerX + a * q.centerY), hs, hab, ?_, ?_⟩
  · intro k; dsimp only; rw [hx k]; ring
  · intro k; dsimp only; rw [hy k]; ring

noncomputable def gaugedRealRepresentative (q : PhysicalCentralConfiguration n mass)
    (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j) : NormalizedSystem ℝ n mass :=
  Classical.choose (q.exists_gauged_similar hm i j hij)

theorem gaugedRealRepresentative_spec (q : PhysicalCentralConfiguration n mass)
    (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j) :
    (q.gaugedRealRepresentative hm i j hij).InGauge i j ∧
      PlanarSimilar (q.x, q.y)
        ((q.gaugedRealRepresentative hm i j hij).x, (q.gaugedRealRepresentative hm i j hij).y) :=
  Classical.choose_spec (q.exists_gauged_similar hm i j hij)

end PhysicalCentralConfiguration

noncomputable def physicalClassToGauge {n : ℕ} {mass : Fin n → ℝ}
    (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j)
    (c : PhysicalSimilarityClass n mass) :
    {q : NormalizedSystem ℂ n (fun k => (mass k : ℂ)) // q.InGauge i j} :=
  ⟨(c.out.gaugedRealRepresentative hm i j hij).map Complex.ofRealHom,
    NormalizedSystem.map_inGauge _ _ (c.out.gaugedRealRepresentative_spec hm i j hij).1⟩

theorem physicalClassToGauge_injective {n : ℕ} {mass : Fin n → ℝ}
    (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j) :
    Function.Injective (physicalClassToGauge hm i j hij) := by
  intro c d he
  let p := c.out.gaugedRealRepresentative hm i j hij
  let q := d.out.gaugedRealRepresentative hm i j hij
  have hxy : (p.x, p.y) = (q.x, q.y) := by
    apply Prod.ext
    · funext k
      exact Complex.ofReal_injective (congrArg (fun z => z.val.x k) he)
    · funext k
      exact Complex.ofReal_injective (congrArg (fun z => z.val.y k) he)
  have hp : PlanarSimilar (c.out.x, c.out.y) (p.x, p.y) :=
    (c.out.gaugedRealRepresentative_spec hm i j hij).2
  have hq : PlanarSimilar (d.out.x, d.out.y) (q.x, q.y) :=
    (d.out.gaugedRealRepresentative_spec hm i j hij).2
  rw [hxy] at hp
  exact Quotient.out_equiv_out.mp (hp.trans hq.symm)

theorem finite_physical_classes_of_finite_gauged {n : ℕ} (mass : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j)
    (h : {q : NormalizedSystem ℂ n (fun k => (mass k : ℂ)) | q.InGauge i j}.Finite) :
    Finite (PhysicalSimilarityClass n mass) := by
  letI : Finite {q : NormalizedSystem ℂ n (fun k => (mass k : ℂ)) // q.InGauge i j} :=
    Set.finite_coe_iff.mpr h
  exact Finite.of_injective _ (physicalClassToGauge_injective hm i j hij)

theorem infinite_gauged_of_infinite_physical_classes {n : ℕ} (mass : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j)
    [Infinite (PhysicalSimilarityClass n mass)] :
    {q : NormalizedSystem ℂ n (fun k => (mass k : ℂ)) | q.InGauge i j}.Infinite := by
  intro hf
  letI : Finite (PhysicalSimilarityClass n mass) :=
    finite_physical_classes_of_finite_gauged mass hm i j hij hf
  exact not_finite (PhysicalSimilarityClass n mass)

end CentralConfigurations
