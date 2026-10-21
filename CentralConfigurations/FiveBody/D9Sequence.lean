import CentralConfigurations.FiveBody.D9Virial
import CentralConfigurations.Asymptotics.TwoColor
import CentralConfigurations.Asymptotics.ClusterPairLimits
import CentralConfigurations.Model.ZWMassCenter


/-!
# D9 sequence identities and skew-attachment exclusion

The hypotheses specify ratios of the original positions and inverse
distances. D9OrderConstructors.lean and D9RawExclusion.lean connect these
estimates to the diagram support. The triple-potential limit is derived
from the force and metric equations.
-/

namespace CentralConfigurations.FiveBody.D9
open Filter Asymptotics
open scoped Topology

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}

theorem triple_div_zero {c d : ℕ → ℂ}
    (hfree : ∀ i : Fin 5, i.val < 3 →
      Tendsto (fun t => ((q t).w i - c t) * (q t).z i / d t) atTop (𝓝 0))
    (hforce : ∀ i : Fin 5, i.val < 3 →
      Tendsto (fun t => ((q t).w i - c t) * exteriorZ (q t) i / d t) atTop (𝓝 0)) :
    Tendsto (fun t => triplePotential (q t) / d t) atTop (𝓝 0) := by
  have h0 := ((hfree 0 (by decide)).sub (hforce 0 (by decide))).const_mul (mass 0)
  have h1 := ((hfree 1 (by decide)).sub (hforce 1 (by decide))).const_mul (mass 1)
  have h2 := ((hfree 2 (by decide)).sub (hforce 2 (by decide))).const_mul (mass 2)
  convert (h0.add h1).add h2 using 1
  · funext t
    rw [centered_triple_virial (q t) (c t)]
    ring
  · ring

theorem triple_zero {c : ℕ → ℂ}
    (hw : ∀ i : Fin 5, i.val < 3 → Tendsto (fun t => (q t).w i - c t) atTop (𝓝 0))
    (hz : ∀ i : Fin 5, i.val < 3 → Tendsto (fun t => (q t).z i) atTop (𝓝 0))
    (hE : ∀ i : Fin 5, i.val < 3 → Tendsto (fun t => exteriorZ (q t) i) atTop (𝓝 0)) :
    Tendsto (fun t => triplePotential (q t)) atTop (𝓝 0) := by
  have h := triple_div_zero (d := fun _ => 1)
    (fun i hi => by simpa using (hw i hi).mul (hz i hi))
    (fun i hi => by simpa using (hw i hi).mul (hE i hi))
  simpa using h

def Cross (i a : Fin 5) : Prop := i.val < 3 ∧ 3 ≤ a.val
def External (i a : Fin 5) : Prop := Cross i a ∨ (i = 3 ∧ a = 4)

/-- The skew rate interface uses no power-law or Puiseux ansatz.  All ratios
are taken on actual solutions.  The dominant inverse is the 0--3 attachment. -/
structure SkewRatios (q : ℕ → ZWSystem ℂ 5 mass) where
  center : ℕ → ℂ
  z_zero : ∀ i : Fin 5, i.val < 3 → Tendsto (fun t => (q t).z i) atTop (𝓝 0)
  centered_w_zero : ∀ i : Fin 5, i.val < 3 →
    Tendsto (fun t => (q t).w i - center t) atTop (𝓝 0)
  cross_ratio_zero : ∀ i a, Cross i a →
    Tendsto (fun t => ((q t).w i - center t) / ((q t).w i - (q t).w a)) atTop (𝓝 0)
  inverse_ratios : ∀ i a, External i a →
    Tendsto (fun t => (q t).delta i a / (q t).delta 0 3) atTop
      (𝓝 (if i = 0 ∧ a = 3 then 1 else 0))
  dominant_reciprocal_zero :
    Tendsto (fun t => ((q t).delta 0 3)⁻¹) atTop (𝓝 0)

theorem SkewRatios.triple_div_zero (h : SkewRatios q) :
    Tendsto (fun t => triplePotential (q t) / (q t).delta 0 3) atTop (𝓝 0) := by
  apply D9.triple_div_zero (c := h.center)
  · intro i hi
    simpa only [mul_zero, div_eq_mul_inv] using
      ((h.centered_w_zero i hi).mul (h.z_zero i hi)).mul h.dominant_reciprocal_zero
  · intro i hi
    have term (a : Fin 5) (ha : 3 ≤ a.val) :
        Tendsto (fun t => ((q t).w i - h.center t) * (q t).zForce i a /
          (q t).delta 0 3) atTop (𝓝 0) := by
      have hij : i ≠ a := by intro he; subst a; omega
      have hh := (h.cross_ratio_zero i a ⟨hi, ha⟩).mul
        (h.inverse_ratios i a (Or.inl ⟨hi, ha⟩))
      simp only [zero_mul] at hh
      convert hh using 1
      funext t
      rw [zForce_eq_delta_div_w (q t) i a hij]
      ring
    have h3 := (term 3 (by decide)).const_mul (mass 3)
    have h4 := (term 4 (by decide)).const_mul (mass 4)
    convert h3.add h4 using 1
    · funext t; dsimp [exteriorZ]; ring
    · ring

theorem SkewRatios.potential_div_limit (h : SkewRatios q) :
    Tendsto (fun t => (q t).toNormalized.unorderedPotential / (q t).delta 0 3)
      atTop (𝓝 (mass 0 * mass 3)) := by
  have term (i a : Fin 5) (ha : External i a) :=
    (h.inverse_ratios i a ha).const_mul (mass i * mass a)
  have he := ((((((term 0 3 (by norm_num [External, Cross])).add (term 0 4 (by norm_num [External, Cross]))).add
    (term 1 3 (by norm_num [External, Cross]))).add (term 1 4 (by norm_num [External, Cross]))).add
    (term 2 3 (by norm_num [External, Cross]))).add (term 2 4 (by norm_num [External, Cross]))).add (term 3 4 (by norm_num [External, Cross]))
  have hh := h.triple_div_zero.add he
  norm_num [Fin.ext_iff] at hh
  convert hh using 1
  · funext t; rw [potential_decomposition]; dsimp [exteriorPotential]; ring

/-- Arbitrary skew attachment rates are excluded at every fixed finite
potential.  The complete triple residual is derived, never assumed. -/
theorem SkewRatios.false_of_constant_potential (h : SkewRatios q)
    (hm0 : mass 0 ≠ 0) (hm3 : mass 3 ≠ 0) (I0 : ℂ)
    (hI : ∀ t, (q t).toNormalized.unorderedPotential = I0) : False := by
  have hzero : Tendsto
      (fun t => (q t).toNormalized.unorderedPotential / (q t).delta 0 3) atTop (𝓝 0) := by
    simpa only [hI, div_eq_mul_inv, mul_zero] using
      h.dominant_reciprocal_zero.const_mul I0
  exact mul_ne_zero hm0 hm3 (tendsto_nhds_unique h.potential_div_limit hzero)

end CentralConfigurations.FiveBody.D9



