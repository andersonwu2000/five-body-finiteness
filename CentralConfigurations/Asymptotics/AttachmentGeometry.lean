import CentralConfigurations.Asymptotics.ClusterOrigin
import CentralConfigurations.Asymptotics.OneStrokeClusterLimits
import CentralConfigurations.Diagrams.ExternalQuadrilateralRows

/-!
# A close singleton attachment at a secondary triangle scale

Section 11.12 uses a near external body whose z-position is nonzero on the
triangle scale. The actual force equations, rather than a leading-row table,
give dominance at this body and coincidence of its normalized w-position
with the attached triangle vertex. The hypotheses below keep all omitted
separation comparisons explicit; the source diagram discharges them later.
-/

namespace CentralConfigurations

open Filter Asymptotics
open scoped Topology BigOperators

namespace PairEstimateData

theorem w_from_wForce_and_z (p : PairEstimateData) (t : ℕ) :
    (p.wForce t)⁻¹ ^ 2 * ((p.z t)⁻¹) ^ 3 = p.w t := by
  have h : p.wForce t ^ 2 = (p.w t * p.z t ^ 3)⁻¹ := p.swap.zForce_sq_inverse t
  rw [inv_pow, h, inv_inv]
  change (p.w t * p.z t ^ 3) * (p.z t)⁻¹ ^ 3 = p.w t
  field_simp [p.z_ne_zero t]

/-- A close z-attachment with bounded relative w-force has a w-separation
strictly larger than the reference internal w-separation. -/
theorem w_littleO_of_z_littleO_and_wForce_bigO (p r : PairEstimateData)
    (hz : p.z =o[atTop] r.z) (hf : p.wForce =O[atTop] r.wForce) :
    r.w =o[atTop] p.w := by
  have hfi := hf.inv_rev (Eventually.of_forall fun t h =>
    (p.wForce_ne_zero t h).elim)
  have hzi := hz.inv_rev (Eventually.of_forall fun t h =>
    (p.z_ne_zero t h).elim)
  exact ((hfi.pow 2).mul_isLittleO (hzi.pow (by decide : 0 < 3))).congr
    (fun t => r.w_from_wForce_and_z t) (fun t => p.w_from_wForce_and_z t)

end PairEstimateData

namespace ZWSystem

variable {n : ℕ} {mass : Fin n → ℂ}

/-- Bounds on every force term bound the actual w-position. -/
theorem w_position_bigO_of_forces (q : ℕ → ZWSystem ℂ n mass)
    (b : ℕ → ℂ) (i : Fin n)
    (hf : ∀ k, (fun t => (q t).wForce i k) =O[atTop] b) :
    (fun t => (q t).w i) =O[atTop] b := by
  have hs : (fun t => ∑ k, mass k * (q t).wForce i k) =O[atTop] b :=
    IsBigO.sum (fun k _ => (hf k).const_mul_left (mass k))
  exact hs.congr_left (fun t => by
    simpa only [wForce, mul_assoc] using ((q t).force_w i).symm)

/-- The row equation bounds one omitted force once the position and all
remaining terms have been bounded. -/
theorem wForce_bigO_of_row (q : ℕ → ZWSystem ℂ n mass)
    (b : ℕ → ℂ) (i j : Fin n) (hmj : mass j ≠ 0)
    (hp : (fun t => (q t).w i) =O[atTop] b)
    (hf : ∀ k, k ≠ j → (fun t => (q t).wForce i k) =O[atTop] b) :
    (fun t => (q t).wForce i j) =O[atTop] b := by
  have hs : (fun t => ∑ k ∈ Finset.univ.erase j, mass k * (q t).wForce i k)
      =O[atTop] b := IsBigO.sum (fun k hk =>
        (hf k (Finset.mem_erase.mp hk).1).const_mul_left (mass k))
  apply (isBigO_const_mul_left_iff hmj).mp
  exact (hp.sub hs).congr_left (fun t => by
    have he := Finset.sum_erase_add (s := Finset.univ)
      (f := fun k => mass k * (q t).wForce i k) (Finset.mem_univ j)
    have hr : (∑ k, mass k * (q t).wForce i k) = (q t).w i := by
      simpa only [wForce, mul_assoc] using ((q t).force_w i).symm
    rw [hr] at he
    linear_combination -he)

/-- The same-pair separation/force ratios agree in both colors. -/
theorem w_separation_div_force_eq_z (q : ZWSystem ℂ n mass)
    (i j : Fin n) (hij : i ≠ j) :
    (q.w i - q.w j) / q.wForce i j = (q.z i - q.z j) / q.zForce i j := by
  apply (div_eq_div_iff (q.wForce_ne_zero i j hij) (q.zForce_ne_zero i j hij)).mpr
  dsimp [wForce, zForce]
  ring

/-- The near pair dominates both force rows at the singleton endpoint.
Its w-separation is then negligible compared with its own w-force. -/
theorem close_attachment_force_dominance (q : ℕ → ZWSystem ℂ n mass)
    (p i : Fin n) (hpi : p ≠ i) (hmi : mass i ≠ 0)
    (hnear : (fun t => (q t).z p - (q t).z i) =o[atTop] (fun t => (q t).z p))
    (hfar : ∀ k, k ≠ p → k ≠ i → (fun t => (q t).z p) =O[atTop]
      (fun t => (q t).z p - (q t).z k))
    (hw : ∀ k, k ≠ p → k ≠ i →
      (fun t => (q t).w p - (q t).w i) =O[atTop]
        (fun t => (q t).w p - (q t).w k)) :
    (∀ k, k ≠ p → k ≠ i →
      (fun t => (q t).zForce p k) =o[atTop] (fun t => (q t).zForce p i)) ∧
    (∀ k, k ≠ p → k ≠ i →
      (fun t => (q t).wForce p k) =o[atTop] (fun t => (q t).wForce p i)) ∧
    (fun t => (q t).w p - (q t).w i) =o[atTop] (fun t => (q t).wForce p i) := by
  have hF (k : Fin n) (hkp : k ≠ p) (hki : k ≠ i) :=
    zForce_littleO_of_close_pair q p i k hpi hkp.symm
      (hnear.trans_isBigO (hfar k hkp hki)) (hw k hkp hki)
  have hG (k : Fin n) (hkp : k ≠ p) (hki : k ≠ i) :=
    wForce_littleO_of_close_pair q p i k hpi hkp.symm
      (hnear.trans_isBigO (hfar k hkp hki)) (hw k hkp hki)
  have hdom := z_position_theta_dominant_force q p i hpi hmi hF
  have hsep := (hnear.trans_isBigO hdom.1).tendsto_div_nhds_zero
  refine ⟨hF, hG, (isLittleO_iff_tendsto
    (fun t h => ((q t).wForce_ne_zero p i hpi h).elim)).mpr ?_⟩
  simpa only [w_separation_div_force_eq_z _ p i hpi] using hsep

end ZWSystem

/-- A two-body cluster of nonzero total mass inherits the smallness of its
weighted center and diameter. No order or positivity of the complex masses
is needed beyond their nonzero sum. -/
theorem two_point_cluster_positions_small {f g b : ℕ → ℂ} (a c : ℂ)
    (hac : a + c ≠ 0)
    (hcenter : (fun t => a * f t + c * g t) =o[atTop] b)
    (hdiam : (fun t => f t - g t) =o[atTop] b) :
    f =o[atTop] b ∧ g =o[atTop] b := by
  have hf : f =o[atTop] b :=
    ((hcenter.add (hdiam.const_mul_left c)).const_mul_left (a + c)⁻¹).congr_left
      (fun t => by field_simp [hac]; ring)
  refine ⟨hf, ?_⟩
  exact (hf.sub hdiam).congr_left (fun t => by ring)

end CentralConfigurations
