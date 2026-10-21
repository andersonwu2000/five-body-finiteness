import CentralConfigurations.Diagrams.BoundedPotentialRule
import CentralConfigurations.Enumeration.DistanceOrderDomains

/-!
# The bounded-potential implication behind Rule 2h

A shrinking distance cannot be strictly smaller than every other distance.
Consequently an actual radius level below 3 cannot be a unique strict minimum.
The executable domain check proves that implication for all admitted radius
assignments. Counting singleton {2} domains alone is not substituted for
counting actual level-2 distances when nonsingleton distance domains occur.
-/

namespace CentralConfigurations

open scoped Topology BigOperators
open Filter Asymptotics

theorem ZWSystem.delta_ne_zero {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) : q.delta i j ≠ 0 := by
  intro hz
  have h := q.distance i j hij
  simp [hz] at h

theorem ZWSystem.no_unique_shrinking_pair {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i j : Fin n) (hij : i < j)
    (hmi : mass i ≠ 0) (hmj : mass j ≠ 0)
    (hs : (fun t => ((q t).delta i j)⁻¹) =o[atTop] (fun _ => (1 : ℂ)))
    (ho : ∀ k m, k < m → (k, m) ≠ (i, j) →
      (fun t => ((q t).delta i j)⁻¹) =o[atTop] (fun t => ((q t).delta k m)⁻¹)) : False := by
  let r : ℕ → ℂ := fun t => (q t).delta i j
  let f : (Fin n × Fin n) → ℕ → ℂ := fun p t =>
    if p.1 < p.2 then mass p.1 * mass p.2 * (q t).delta p.1 p.2 else 0
  have hnr : ∀ t, r t ≠ 0 := fun t => (q t).delta_ne_zero i j hij.ne
  have hone : (fun _ => (1 : ℂ)) =o[atTop] r := by
    simpa only [inv_one, inv_inv] using hs.inv_rev
      (Eventually.of_forall fun t h => (inv_ne_zero (hnr t) h).elim)
  have hsum : (fun t => ∑ p, f p t) =o[atTop] r := by
    have hp := (ZWSystem.unorderedPotential_isBigO_one q atTop).trans_isLittleO hone
    simpa only [f, Fintype.sum_prod_type, NormalizedSystem.unorderedPotential,
      ZWSystem.toNormalized] using hp
  have hi : f (i, j) =Θ[atTop] r := by
    simpa only [f, if_pos hij] using
      (isTheta_refl r atTop).const_mul_left (mul_ne_zero hmi hmj)
  apply finite_sum_cannot_have_unique_leading_term f r (i, j) hnr hi ?_ hsum
  rintro ⟨k, m⟩ hkm
  by_cases hlt : k < m
  · have hd : (fun t => (q t).delta k m) =o[atTop] r := by
      simpa only [inv_inv] using (ho k m hlt hkm).inv_rev
        (Eventually.of_forall fun t h => (inv_ne_zero (hnr t) h).elim)
    simpa only [f, if_pos hlt] using hd.const_mul_left (mass k * mass m)
  · simpa only [f, if_neg hlt] using (isLittleO_zero r atTop)

def noUniqueShrinkingRadiusCheck {n : ℕ} (D : OrderBox (ROrderIndex n)) : Bool :=
  decide (∀ p : ROrderIndex n, ¬ ((D p).sup id < 3 ∧
    ∀ r : ROrderIndex n, r ≠ p → ∀ a ∈ D r, (D p).sup id < a))

def shrinkingRadiusCheck {n : ℕ} (d : DiagramCode n)
    (B : OrderBox (ZWOrderIndex n)) : Bool :=
  noUniqueShrinkingRadiusCheck (producedDistanceBox d B)

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

theorem exists_other_radius_level_le (p : ROrderIndex n)
    (hm₁ : mass p.1.1 ≠ 0) (hm₂ : mass p.1.2 ≠ 0)
    (hs : o.radiusCode p < 3) :
    ∃ r : ROrderIndex n, r ≠ p ∧ o.radiusCode r ≤ o.radiusCode p := by
  by_contra hn
  apply ZWSystem.no_unique_shrinking_pair q p.1.1 p.1.2 p.2 hm₁ hm₂
  · exact (o.radius_level p.1.1 p.1.2).lt_three_iff_littleO_middle.mp hs
  · intro k m hkm hne
    have hl : o.radiusCode p < o.radiusCode ⟨(k, m), hkm⟩ := by
      apply lt_of_not_ge
      intro hle
      exact hn ⟨⟨(k, m), hkm⟩, fun heq => hne (congrArg Subtype.val heq), hle⟩
    exact (o.radius_level p.1.1 p.1.2).littleO_of_lt (o.radius_level k m) hl

theorem noUniqueShrinkingRadiusCheck_of_admitted (D : OrderBox (ROrderIndex n))
    (hD : D.Admits o.radiusCode) (hm : ∀ i, mass i ≠ 0) :
    noUniqueShrinkingRadiusCheck D = true := by
  apply decide_eq_true
  intro p
  rintro ⟨hs, ho⟩
  have hp := Finset.le_sup (f := id) (hD p)
  obtain ⟨r, hr, hle⟩ := o.exists_other_radius_level_le p (hm _) (hm _) (hp.trans_lt hs)
  exact (not_lt_of_ge (hle.trans hp)) (ho r hr _ (hD r))

variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem shrinkingRadiusCheck_of_admitted (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (hm : ∀ i, mass i ≠ 0) :
    shrinkingRadiusCheck l.diagramCode B = true :=
  o.noUniqueShrinkingRadiusCheck_of_admitted _ (o.admitted_producedDistanceBox l hb B hB) hm

/-- This counts actual radius levels, not singleton entries in a covering box. -/
theorem radius_level_two_count_ne_one (hm : ∀ i, mass i ≠ 0)
    (hnoOne : ∀ p : ROrderIndex n, o.radiusCode p ≠ 1) :
    ((Finset.univ : Finset (ROrderIndex n)).filter (fun p => o.radiusCode p = 2)).card ≠ 1 := by
  intro hcard
  obtain ⟨p, hp⟩ := Finset.card_eq_one.mp hcard
  have hp₂ : o.radiusCode p = 2 := by
    have hmem : p ∈ (Finset.univ : Finset (ROrderIndex n)).filter
        (fun r => o.radiusCode r = 2) := by rw [hp]; simp
    exact (Finset.mem_filter.mp hmem).2
  obtain ⟨r, hrp, hr⟩ := o.exists_other_radius_level_le p (hm _) (hm _) (by rw [hp₂]; decide)
  have hr₀ : o.radiusCode r ≠ 0 := o.radius_ne_zero hb r.1.1 r.1.2 r.2.ne
  have hr₁ := hnoOne r
  have hr₂ : o.radiusCode r = 2 := by omega
  have hmem : r ∈ (Finset.univ : Finset (ROrderIndex n)).filter
      (fun r => o.radiusCode r = 2) := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr₂⟩
  rw [hp, Finset.mem_singleton] at hmem
  exact hrp hmem

end SequenceOrderAssignment

theorem ZWOrderCoverage.filter_shrinkingRadiusCheck {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : ∀ i, mass i ≠ 0) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (C.filter (fun B => shrinkingRadiusCheck l.diagramCode B = true)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨B, Finset.mem_filter.mpr ⟨hB,
    o.shrinkingRadiusCheck_of_admitted (l.comp φ hφ.tendsto_atTop)
      (fun t => hb (φ t)) B ho hm⟩, ho⟩

end CentralConfigurations
