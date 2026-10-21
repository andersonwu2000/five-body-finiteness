import CentralConfigurations.Asymptotics.EpsilonOrderScales
import CentralConfigurations.Asymptotics.OrderLevelComparison

/-!
# One order assignment for every variable of an actual singular sequence

The diagonal of each coordinate matrix stores positions; the off-diagonal
stores oriented separations. Distance entries keep the inverse-distance
branch of the polynomial solution. Their diagonal is zero and is ignored
when forming the source's distance order matrix.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

def ScaledZWLimit.comp {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) : ScaledZWLimit (q ∘ φ) (a ∘ φ) where
  z := l.z
  w := l.w
  z_position i := (l.z_position i).comp hφ
  w_position i := (l.w_position i).comp hφ
  z_force i j := (l.z_force i j).comp hφ
  w_force i j := (l.w_force i j).comp hφ

noncomputable def ExtractedZWLimit.refine {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} (l : ExtractedZWLimit q)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) : ExtractedZWLimit q where
  subsequence := l.subsequence ∘ φ
  strictMono := l.strictMono.comp hφ
  leading := l.leading.comp φ hφ.tendsto_atTop
  z_nonzero := l.z_nonzero
  w_nonzero := l.w_nonzero

namespace ZWSystem

variable {n : ℕ} {mass : Fin n → ℂ}

theorem epsilon_tendsto_zero_of_inverseScale (q : ℕ → ZWSystem ℂ n mass)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    Tendsto (fun t => ((q t).epsilon : ℂ)) atTop (𝓝 0) := by
  have hr : Tendsto (fun t => ‖(q t).zVector‖⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [inverseScale, ← Complex.ofReal_inv, Complex.ofReal_re, Complex.zero_re]
      using (Complex.continuous_re.tendsto 0).comp ha
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hr
  have he : Tendsto (fun t => (q t).epsilon) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_inv, Real.sqrt_zero, epsilon] using hs
  simpa only [Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp he

noncomputable def zOrderValue (q : ZWSystem ℂ n mass) (i j : Fin n) : ℂ :=
  if i = j then q.z i else q.z i - q.z j

noncomputable def wOrderValue (q : ZWSystem ℂ n mass) (i j : Fin n) : ℂ :=
  if i = j then q.w i else q.w i - q.w j

noncomputable def radiusOrderValue (q : ZWSystem ℂ n mass) (i j : Fin n) : ℂ :=
  (q.delta i j)⁻¹

noncomputable def orderPositionScales (q : ℕ → ZWSystem ℂ n mass)
    (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) : OrderScales :=
  epsilonPositionScales (fun t => ((q t).epsilon : ℂ))
    (fun t => Complex.ofReal_ne_zero.mpr (ne_of_gt ((q t).epsilon_pos i₀ j₀ hij₀)))
    (epsilon_tendsto_zero_of_inverseScale q ha)

noncomputable def orderDistanceScales (q : ℕ → ZWSystem ℂ n mass)
    (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) : OrderScales :=
  epsilonDistanceScales (fun t => ((q t).epsilon : ℂ))
    (fun t => Complex.ofReal_ne_zero.mpr (ne_of_gt ((q t).epsilon_pos i₀ j₀ hij₀)))
    (epsilon_tendsto_zero_of_inverseScale q ha)

theorem zOrderValue_upper (q : ℕ → ZWSystem ℂ n mass) (i j : Fin n) :
    (fun t => (q t).zOrderValue i j) =O[atTop]
      (fun t => (((q t).epsilon : ℂ)⁻¹) ^ 2) := by
  by_cases hij : i = j
  · subst j
    apply IsBigO.of_bound 1 (Eventually.of_forall fun t => ?_)
    simpa only [zOrderValue, if_pos rfl, epsilon_scale, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), one_mul] using (q t).norm_z_le i
  · apply IsBigO.of_bound 2 (Eventually.of_forall fun t => ?_)
    simpa only [zOrderValue, if_neg hij, epsilon_scale, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using (q t).norm_z_separation_le i j

theorem wOrderValue_upper (q : ℕ → ZWSystem ℂ n mass)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (i j : Fin n) :
    (fun t => (q t).wOrderValue i j) =O[atTop]
      (fun t => (((q t).epsilon : ℂ)⁻¹) ^ 2) := by
  have h := zOrderValue_upper (fun t => (q t).swap) i j
  simpa only [zOrderValue, wOrderValue, swap, epsilon_scale, hb] using h

theorem radiusOrderValue_upper (q : ℕ → ZWSystem ℂ n mass)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (i j : Fin n) :
    (fun t => (q t).radiusOrderValue i j) =O[atTop]
      (fun t => (((q t).epsilon : ℂ)⁻¹) ^ 2) := by
  by_cases hij : i = j
  · subst j
    simp only [radiusOrderValue, delta_diagonal, inv_zero]
    exact isBigO_zero _ _
  · exact (pairEstimateData q hb i j hij).radius_upper

end ZWSystem

/-- A concrete assignment, rather than an assumed matrix of possible levels. -/
structure SequenceOrderAssignment {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) where
  z : Fin n → Fin n → Fin 6
  w : Fin n → Fin n → Fin 6
  radius : Fin n → Fin n → Fin 6
  z_level : ∀ i j, HasOrderLevel (ZWSystem.orderPositionScales q i₀ j₀ hij₀ ha)
    (fun t => (q t).zOrderValue i j) (z i j)
  w_level : ∀ i j, HasOrderLevel (ZWSystem.orderPositionScales q i₀ j₀ hij₀ ha)
    (fun t => (q t).wOrderValue i j) (w i j)
  radius_level : ∀ i j, HasOrderLevel (ZWSystem.orderDistanceScales q i₀ j₀ hij₀ ha)
    (fun t => (q t).radiusOrderValue i j) (radius i j)

/-- The additional extraction is common to all positions, separations and
distances, including variables of both colors. -/
theorem exists_sequenceOrderAssignment {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, ∃ hφ : StrictMono φ,
      Nonempty (SequenceOrderAssignment (q ∘ φ) i₀ j₀ hij₀ (ha.comp hφ.tendsto_atTop)) := by
  let s := ZWSystem.orderPositionScales q i₀ j₀ hij₀ ha
  let d := ZWSystem.orderDistanceScales q i₀ j₀ hij₀ ha
  let scale (p : Fin 3 × Fin n × Fin n) : OrderScales := ![s, s, d] p.1
  let value (p : Fin 3 × Fin n × Fin n) : ℕ → ℂ :=
    ![(fun t => (q t).zOrderValue p.2.1 p.2.2),
      (fun t => (q t).wOrderValue p.2.1 p.2.2),
      (fun t => (q t).radiusOrderValue p.2.1 p.2.2)] p.1
  have hv : ∀ p, value p =O[atTop] (scale p).upper := by
    rintro ⟨c, i, j⟩
    fin_cases c
    · exact ZWSystem.zOrderValue_upper q i j
    · exact ZWSystem.wOrderValue_upper q hb i j
    · exact ZWSystem.radiusOrderValue_upper q hb i j
  obtain ⟨φ, hφ, k, hk⟩ := exists_simultaneous_order_levels_for_scales scale value hv
  refine ⟨φ, hφ, ⟨{
    z := fun i j => k (0, i, j)
    w := fun i j => k (1, i, j)
    radius := fun i j => k (2, i, j)
    z_level := fun i j => hk (0, i, j)
    w_level := fun i j => hk (1, i, j)
    radius_level := fun i j => hk (2, i, j)
  }⟩⟩

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

theorem z_symm (i j : Fin n) : o.z i j = o.z j i := by
  apply (o.z_level i j).unique
  apply (o.z_level j i).congr_norm
  intro t
  by_cases hij : i = j
  · subst j; rfl
  · simp only [ZWSystem.zOrderValue, if_neg hij, if_neg (Ne.symm hij), norm_sub_rev]

theorem w_symm (i j : Fin n) : o.w i j = o.w j i := by
  apply (o.w_level i j).unique
  apply (o.w_level j i).congr_norm
  intro t
  by_cases hij : i = j
  · subst j; rfl
  · simp only [ZWSystem.wOrderValue, if_neg hij, if_neg (Ne.symm hij), norm_sub_rev]

theorem radius_symm (i j : Fin n) : o.radius i j = o.radius j i := by
  apply (o.radius_level i j).unique
  apply (o.radius_level j i).congr_norm
  intro t
  rw [ZWSystem.radiusOrderValue, ZWSystem.radiusOrderValue, (q t).delta_symm j i]

theorem z_ne_zero (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j : Fin n) (hij : i ≠ j) : o.z i j ≠ 0 := by
  apply (o.z_level i j).ne_zero_of_lower_bound
  simpa only [ZWSystem.zOrderValue, if_neg hij] using
    (ZWSystem.pairEstimateData q hb i j hij).z_lower

theorem w_ne_zero (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j : Fin n) (hij : i ≠ j) : o.w i j ≠ 0 := by
  apply (o.w_level i j).ne_zero_of_lower_bound
  simpa only [ZWSystem.wOrderValue, if_neg hij] using
    (ZWSystem.pairEstimateData q hb i j hij).w_lower

theorem radius_ne_zero (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j : Fin n) (hij : i ≠ j) : o.radius i j ≠ 0 :=
  (o.radius_level i j).ne_zero_of_lower_bound
    (ZWSystem.pairEstimateData q hb i j hij).radius_lower

theorem z_separation_level (i j : Fin n) (hij : i ≠ j) :
    HasOrderLevel (ZWSystem.orderPositionScales q i₀ j₀ hij₀ ha)
      (fun t => (q t).z i - (q t).z j) (o.z i j) := by
  simpa only [ZWSystem.zOrderValue, if_neg hij] using o.z_level i j

theorem w_separation_level (i j : Fin n) (hij : i ≠ j) :
    HasOrderLevel (ZWSystem.orderPositionScales q i₀ j₀ hij₀ ha)
      (fun t => (q t).w i - (q t).w j) (o.w i j) := by
  simpa only [ZWSystem.wOrderValue, if_neg hij] using o.w_level i j

theorem z_position_level (i : Fin n) :
    HasOrderLevel (ZWSystem.orderPositionScales q i₀ j₀ hij₀ ha)
      (fun t => (q t).z i) (o.z i i) := by
  simpa only [ZWSystem.zOrderValue, if_pos rfl] using o.z_level i i

theorem w_position_level (i : Fin n) :
    HasOrderLevel (ZWSystem.orderPositionScales q i₀ j₀ hij₀ ha)
      (fun t => (q t).w i) (o.w i i) := by
  simpa only [ZWSystem.wOrderValue, if_pos rfl] using o.w_level i i

end SequenceOrderAssignment

end CentralConfigurations
