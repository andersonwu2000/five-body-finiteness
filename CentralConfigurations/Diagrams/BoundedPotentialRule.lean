import CentralConfigurations.Asymptotics.PairEstimates
import CentralConfigurations.Diagrams.MatrixRules
import CentralConfigurations.Model.Virial
import CentralConfigurations.Asymptotics.PotentialBounds

/-!
# Bounded potential excludes a unique double edge

This is the corollary of Rule 2h (Chang, printed p. 13), used by the first
branch of Appendix I's `Rule2CSQ` (p. 112). It is distinct from the local
two-column-sums rule. Its proof uses the boundedness of the original
unordered potential. The proved Lemma 2.2 supplies that boundedness for
all normalized solutions, so it is not an additional hypothesis.

A double edge contributes at order epsilon^(-1) to U. Every other pair
contributes little-o of that order if it is not double. A bounded finite sum
cannot have exactly one such leading term with a nonzero mass coefficient.
All complex inverse-distance branches are retained.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter Asymptotics

theorem finite_sum_cannot_have_unique_leading_term {ι : Type*} [Fintype ι]
    [DecidableEq ι] (f : ι → ℕ → ℂ) (r : ℕ → ℂ) (i : ι)
    (hr : ∀ t, r t ≠ 0) (hi : f i =Θ[atTop] r)
    (ho : ∀ j, j ≠ i → f j =o[atTop] r)
    (hs : (fun t => ∑ j, f j t) =o[atTop] r) : False := by
  have hrest : (fun t => ∑ j ∈ Finset.univ.erase i, f j t) =o[atTop] r :=
    IsLittleO.sum (fun j hj => ho j (Finset.mem_erase.mp hj).1)
  have hsmall : f i =o[atTop] r := (hs.sub hrest).congr_left (fun t => by
    have hsum := Finset.sum_erase_add (s := Finset.univ) (f := fun j => f j t)
      (Finset.mem_univ i)
    linear_combination -hsum)
  exact isLittleO_irrefl (Eventually.of_forall hr).frequently
    (hi.2.trans_isLittleO hsmall)

theorem ZWSystem.epsilon_sq_eq_inverseScale {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) : (q.epsilon : ℂ) ^ 2 = q.inverseScale := by
  simp [ZWSystem.epsilon, ZWSystem.inverseScale, inv_pow,
    ← Complex.ofReal_pow, Real.sq_sqrt]

namespace PairEstimateData

/-- Either absent leading force makes the inverse-distance contribution
strictly smaller than the double-edge contribution. -/
theorem delta_littleO_of_absent (p : PairEstimateData)
    (h : p.zForce =o[atTop] p.scale ∨ p.wForce =o[atTop] p.scale) :
    p.delta =o[atTop] (fun t => (p.eps t)⁻¹) := by
  have hf : (fun t => p.zForce t * p.wForce t) =o[atTop]
      (fun t => p.scale t * p.scale t) := by
    rcases h with hz | hw
    · exact hz.mul_isBigO p.wForce_upper
    · exact p.zForce_upper.mul_isLittleO hw
  have hp : (fun t => p.delta t ^ 4) =o[atTop] (fun t => (p.eps t)⁻¹ ^ 4) :=
    hf.congr (fun t => p.force_product t) (fun t => by dsimp [scale]; ring)
  exact hp.of_pow (by decide : (4 : ℕ) ≠ 0)

end PairEstimateData

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem pair_delta_littleO_of_not_double (i j : Fin n) (hij : i ≠ j)
    (h : l.z.force i j = 0 ∨ l.w.force i j = 0) :
    (fun t => (q t).delta i j) =o[atTop] (fun t => ((q t).epsilon : ℂ)⁻¹) := by
  apply (ZWSystem.pairEstimateData q hb i j hij).delta_littleO_of_absent
  exact h.imp ((l.pair_z_absent_iff hb i j hij).mpr)
    ((l.pair_w_absent_iff hb i j hij).mpr)

theorem exists_other_double_edge
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (i j : Fin n) (hij : i < j) (hmi : mass i ≠ 0) (hmj : mass j ≠ 0)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j ≠ 0) :
    ∃ k m : Fin n, k < m ∧ (k, m) ≠ (i, j) ∧
      l.z.force k m ≠ 0 ∧ l.w.force k m ≠ 0 := by
  by_contra hn
  let r : ℕ → ℂ := fun t => ((q t).epsilon : ℂ)⁻¹
  let f : (Fin n × Fin n) → ℕ → ℂ := fun p t =>
    if p.1 < p.2 then mass p.1 * mass p.2 * (q t).delta p.1 p.2 else 0
  have he : ∀ t, ((q t).epsilon : ℂ) ≠ 0 := fun t =>
    Complex.ofReal_ne_zero.mpr (ne_of_gt ((q t).epsilon_pos i j hij.ne))
  have heps : (fun t => ((q t).epsilon : ℂ)) =o[atTop] (fun _ => (1 : ℂ)) := by
    have hs : (fun t => ((q t).epsilon : ℂ) ^ 2) =o[atTop]
        (fun _ => (1 : ℂ) ^ 2) := by
      simpa only [one_pow, ZWSystem.epsilon_sq_eq_inverseScale] using
        (isLittleO_one_iff ℂ).mpr ha
    exact hs.of_pow (by decide : (2 : ℕ) ≠ 0)
  have hone : (fun _ => (1 : ℂ)) =o[atTop] r := by
    simpa only [inv_one] using heps.inv_rev
      (Eventually.of_forall fun t ht => (he t ht).elim)
  have hsum : (fun t => ∑ p, f p t) =o[atTop] r := by
    have hp := (ZWSystem.unorderedPotential_isBigO_one q atTop).trans_isLittleO hone
    simpa only [f, Fintype.sum_prod_type, NormalizedSystem.unorderedPotential,
      ZWSystem.toNormalized] using hp
  have hd : (fun t => (q t).delta i j) =Θ[atTop] r := by
    have hp := (ZWSystem.pairEstimateData q hb i j hij.ne).double_force_iff_radius.mp
      ⟨(l.pair_z_stroke_iff hb i j hij.ne).mpr hz,
        (l.pair_w_stroke_iff hb i j hij.ne).mpr hw⟩
    simpa only [PairEstimateData.radius, ZWSystem.pairEstimateData, inv_inv] using hp.inv
  have hi : f (i, j) =Θ[atTop] r := by
    simpa only [f, if_pos hij] using hd.const_mul_left (mul_ne_zero hmi hmj)
  apply finite_sum_cannot_have_unique_leading_term f r (i, j)
    (fun t => inv_ne_zero (he t)) hi ?_ hsum
  rintro ⟨k, m⟩ hkm
  by_cases hlt : k < m
  · have hnot : l.z.force k m = 0 ∨ l.w.force k m = 0 := by
      by_cases hk : l.z.force k m = 0
      · exact Or.inl hk
      · exact Or.inr (by
          by_contra hm
          exact hn ⟨k, m, hlt, hkm, hk, hm⟩)
    simpa only [f, if_pos hlt] using
      (l.pair_delta_littleO_of_not_double hb k m hlt.ne hnot).const_mul_left
        (mass k * mass m)
  · simpa only [f, if_neg hlt] using (isLittleO_zero r atTop)

end ScaledZWLimit

/-- The ordered upper triangle counts every double edge exactly once. -/
def doubleEdgePairs {n : ℕ} (A B : Fin n → Fin n → ℕ) : Finset (Fin n × Fin n) :=
  Finset.univ.filter (fun p => p.1 < p.2 ∧ A p.1 p.2 = 1 ∧ B p.1 p.2 = 1)

def NoSingleDoubleEdgeRule {n : ℕ} (A B : Fin n → Fin n → ℕ) : Prop :=
  (doubleEdgePairs A B).card ≠ 1

instance noSingleDoubleEdgeRule_decidable {n : ℕ} (A B : Fin n → Fin n → ℕ) :
    Decidable (NoSingleDoubleEdgeRule A B) := by
  unfold NoSingleDoubleEdgeRule
  infer_instance

theorem ScaledZWLimit.no_single_double_edge_rule {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hm : ∀ i, mass i ≠ 0) : NoSingleDoubleEdgeRule l.z.matrix l.w.matrix := by
  intro h
  obtain ⟨⟨i, j⟩, hp⟩ := Finset.card_eq_one.mp h
  have hmem : (i, j) ∈ doubleEdgePairs l.z.matrix l.w.matrix := by
    rw [hp]
    exact Finset.mem_singleton_self _
  obtain ⟨hij, hz, hw⟩ := (Finset.mem_filter.mp hmem).2
  have hz' : l.z.force i j ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij.ne] using hz
  have hw' : l.w.force i j ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij.ne] using hw
  obtain ⟨k, m, hkm, hne, hk, hm'⟩ :=
    l.exists_other_double_edge hb ha i j hij (hm i) (hm j) hz' hw'
  have hmem' : (k, m) ∈ doubleEdgePairs l.z.matrix l.w.matrix := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hkm, ?_, ?_⟩ <;>
      simp [OneColorLimit.matrix, OneColorLimit.Incident, hkm.ne, hk, hm']
  rw [hp, Finset.mem_singleton] at hmem'
  exact hne hmem'

end CentralConfigurations
