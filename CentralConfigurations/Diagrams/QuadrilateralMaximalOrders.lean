import CentralConfigurations.Diagrams.PathMaximalOrders

/-!
# The quadrilateral exclusion used in Section 11.7

For a same-color quadrilateral with both diagonals absent, three consecutive
opposite-color equation rows cannot all be supported inside the quadrilateral.
The proof explicitly extracts skew subsequences. It does not infer order
comparability merely from the edge-type conclusion of Rule 2g.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

theorem separation_theta_of_littleO {x y z : ℕ → ℂ}
    (h : (fun t => x t - y t) =o[atTop] (fun t => y t - z t)) :
    (fun t => y t - z t) =Θ[atTop] (fun t => x t - z t) := by
  have he (t : ℕ) : (x t - y t) + (y t - z t) = x t - z t := by ring
  exact ⟨h.right_isBigO_add.congr_right he,
    (h.isBigO.add (isBigO_refl _ atTop)).congr_left he⟩

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

/-- If both disjoint short sides are smaller than their connecting side,
two closed rows at one short side force the impossible order-one radius. -/
theorem short_z_quadrilateral_pair_not_closed (hm : AdmissibleMasses mass)
    (i j k r : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hir : i ≠ r)
    (hjk : j ≠ k) (hjr : j ≠ r) (_hkr : k ≠ r)
    (hstroke : l.z.force i j ≠ 0)
    (hs : (fun t => (q t).z i - (q t).z j) =o[atTop]
      (fun t => (q t).z j - (q t).z k))
    (ht : (fun t => (q t).z k - (q t).z r) =o[atTop]
      (fun t => (q t).z j - (q t).z k))
    (hi : MaximalTermCover (fun a t => (q t).wEquationTerm i a) {i, j, k, r})
    (hj : MaximalTermCover (fun a t => (q t).wEquationTerm j a) {i, j, k, r}) :
    False := by
  have hac := separation_theta_of_littleO hs
  have hbd : (fun t => (q t).z j - (q t).z k) =Θ[atTop]
      (fun t => (q t).z j - (q t).z r) := by
    exact ⟨ht.right_isBigO_add.congr_right (fun t => by ring),
      (ht.isBigO.add (isBigO_refl _ atTop)).congr_left (fun t => by ring)⟩
  have had := hbd.trans (separation_theta_of_littleO (hs.trans_isTheta hbd))
  have hsik := hs.trans_isTheta hac
  have hsir := hs.trans_isTheta had
  have hsjr := hs.trans_isTheta hbd
  have hwi_k := l.wForce_littleO_of_z_separation_stroke hb i k i j hik hij hstroke hsik
  have hwi_r := l.wForce_littleO_of_z_separation_stroke hb i r i j hir hij hstroke hsir
  have hwj_k := l.wForce_littleO_of_z_separation_stroke hb j k i j hjk hij hstroke hs
  have hwj_r := l.wForce_littleO_of_z_separation_stroke hb j r i j hjr hij hstroke hsjr
  have hmi : mass i ≠ 0 := by simpa using hm {i} (Finset.singleton_nonempty i)
  have hmj : mass j ≠ 0 := by simpa using hm {j} (Finset.singleton_nonempty j)
  have hti_k : (fun t => (q t).wEquationTerm i k) =o[atTop]
      (fun t => (q t).wEquationTerm i j) := by
    simpa only [ZWSystem.wEquationTerm, if_neg (Ne.symm hik), if_neg (Ne.symm hij)] using
      (hwi_k.const_mul_left (mass k)).const_mul_right hmj
  have hti_r : (fun t => (q t).wEquationTerm i r) =o[atTop]
      (fun t => (q t).wEquationTerm i j) := by
    simpa only [ZWSystem.wEquationTerm, if_neg (Ne.symm hir), if_neg (Ne.symm hij)] using
      (hwi_r.const_mul_left (mass r)).const_mul_right hmj
  have hwji_k : (fun t => (q t).wForce j k) =o[atTop] (fun t => (q t).wForce j i) :=
    hwj_k.neg_right.congr_right (fun t => ((q t).swap.zForce_antisymm j i).symm)
  have hwji_r : (fun t => (q t).wForce j r) =o[atTop] (fun t => (q t).wForce j i) :=
    hwj_r.neg_right.congr_right (fun t => ((q t).swap.zForce_antisymm j i).symm)
  have htj_k : (fun t => (q t).wEquationTerm j k) =o[atTop]
      (fun t => (q t).wEquationTerm j i) := by
    simpa only [ZWSystem.wEquationTerm, if_neg (Ne.symm hjk), if_neg hij] using
      (hwji_k.const_mul_left (mass k)).const_mul_right hmi
  have htj_r : (fun t => (q t).wEquationTerm j r) =o[atTop]
      (fun t => (q t).wEquationTerm j i) := by
    simpa only [ZWSystem.wEquationTerm, if_neg (Ne.symm hjr), if_neg hij] using
      (hwji_r.const_mul_left (mass r)).const_mul_right hmi
  have herase : (({i, j, k, r} : Finset (Fin n)).erase k).erase r = {i, j} := by
    ext a
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hi' : MaximalTermCover (fun a t => (q t).wEquationTerm i a) {i, j} := by
    simpa only [herase] using (hi.erase_of_littleO hti_k).erase_of_littleO hti_r
  have hj' : MaximalTermCover (fun a t => (q t).wEquationTerm j a) {i, j} := by
    simpa only [herase] using (hj.erase_of_littleO htj_k).erase_of_littleO htj_r
  let p := ZWSystem.pairEstimateData q hb i j hij
  let s := ZWSystem.pairEstimateData q hb j k hjk
  have hradius := ZWSystem.two_w_pair_covers_radius_theta_one q hm i j hij hi' hj'
  have hp := (l.pair_z_stroke_iff hb i j hij).mpr hstroke
  have hlarge := (p.stroke_radius_iff_z_maximal hp).mp hradius
  have hsmall : p.z =o[atTop] p.scale := hs.trans_isBigO s.z_upper
  exact isLittleO_irrefl (Eventually.of_forall p.z_ne_zero).frequently
    (hsmall.trans_isTheta hlarge.symm)

/-- The short side of a skew quadrilateral cannot have two closed endpoint
rows. A further extraction handles its opposite side without assuming limits
of separation ratios on the original sequence. -/
theorem smaller_z_quadrilateral_two_covers_impossible (hm : AdmissibleMasses mass)
    (i j k r : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hir : i ≠ r)
    (hjk : j ≠ k) (hjr : j ≠ r) (hkr : k ≠ r)
    (h₁ : l.z.force i j ≠ 0) (h₂ : l.z.force j k ≠ 0)
    (h₃ : l.z.force k r ≠ 0) (h₄ : l.z.force r i ≠ 0)
    (hd₁ : l.z.force i k = 0) (hd₂ : l.z.force j r = 0)
    (hs : (fun t => (q t).z i - (q t).z j) =o[atTop]
      (fun t => (q t).z j - (q t).z k))
    (hi : MaximalTermCover (fun a t => (q t).wEquationTerm i a) {i, j, k, r})
    (hj : MaximalTermCover (fun a t => (q t).wEquationTerm j a) {i, j, k, r}) :
    False := by
  obtain ⟨φ, hφ, ht | ht⟩ := l.z_path_skew_subsequence hb j k r hjk hkr hjr h₂ h₃ hd₂
  · have hs' := hs.comp_tendsto hφ.tendsto_atTop
    have hc := separation_theta_of_littleO hs'
    have hiR := separation_theta_of_littleO (hc.symm.isBigO.trans_isLittleO ht)
    have hcomp : (fun t => (q (φ t)).z k - (q (φ t)).z r) =Θ[atTop]
        (fun t => (q (φ t)).z r - (q (φ t)).z i) := by
      exact ⟨hiR.1.neg_right.congr_right (fun t => by ring),
        hiR.2.neg_left.congr_left (fun t => by ring)⟩
    have hclose := (l.comp φ hφ.tendsto_atTop).comparable_z_path_closes (fun t => hb (φ t))
      k r i hkr (Ne.symm hir) (Ne.symm hik) h₃ h₄ hcomp
    apply hclose
    change l.z.force k i = 0
    rw [l.z.antisymm k i, hd₁, neg_zero]
  · exact (l.comp φ hφ.tendsto_atTop).short_z_quadrilateral_pair_not_closed
      (fun t => hb (φ t)) hm i j k r hij hik hir hjk hjr hkr h₁
      (hs.comp_tendsto hφ.tendsto_atTop) ht
      (hi.comp φ hφ.tendsto_atTop) (hj.comp φ hφ.tendsto_atTop)

/-- Three of the four opposite-color rows suffice: either skew direction
selects an edge whose two endpoint rows are among the three closed rows. -/
theorem z_quadrilateral_three_covers_impossible (hm : AdmissibleMasses mass)
    (i j k r : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hir : i ≠ r)
    (hjk : j ≠ k) (hjr : j ≠ r) (hkr : k ≠ r)
    (h₁ : l.z.force i j ≠ 0) (h₂ : l.z.force j k ≠ 0)
    (h₃ : l.z.force k r ≠ 0) (h₄ : l.z.force r i ≠ 0)
    (hd₁ : l.z.force i k = 0) (hd₂ : l.z.force j r = 0)
    (hi : MaximalTermCover (fun a t => (q t).wEquationTerm i a) {i, j, k, r})
    (hj : MaximalTermCover (fun a t => (q t).wEquationTerm j a) {i, j, k, r})
    (hk : MaximalTermCover (fun a t => (q t).wEquationTerm k a) {i, j, k, r}) :
    False := by
  obtain ⟨φ, hφ, hs | hs⟩ := l.z_path_skew_subsequence hb i j k hij hjk hik h₁ h₂ hd₁
  · exact (l.comp φ hφ.tendsto_atTop).smaller_z_quadrilateral_two_covers_impossible
      (fun t => hb (φ t)) hm i j k r hij hik hir hjk hjr hkr h₁ h₂ h₃ h₄ hd₁ hd₂ hs
      (hi.comp φ hφ.tendsto_atTop) (hj.comp φ hφ.tendsto_atTop)
  · have he : ({k, j, i, r} : Finset (Fin n)) = {i, j, k, r} := by
      ext a
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hs' : (fun t => (q (φ t)).z k - (q (φ t)).z j) =o[atTop]
        (fun t => (q (φ t)).z j - (q (φ t)).z i) :=
      hs.neg_left.neg_right.congr (fun t => by ring) (fun t => by ring)
    have h₂' : l.z.force k j ≠ 0 := by rw [l.z.antisymm k j]; exact neg_ne_zero.mpr h₂
    have h₁' : l.z.force j i ≠ 0 := by rw [l.z.antisymm j i]; exact neg_ne_zero.mpr h₁
    have h₄' : l.z.force i r ≠ 0 := by rw [l.z.antisymm i r]; exact neg_ne_zero.mpr h₄
    have h₃' : l.z.force r k ≠ 0 := by rw [l.z.antisymm r k]; exact neg_ne_zero.mpr h₃
    have hd₁' : l.z.force k i = 0 := by rw [l.z.antisymm k i, hd₁, neg_zero]
    refine (l.comp φ hφ.tendsto_atTop).smaller_z_quadrilateral_two_covers_impossible
      (fun t => hb (φ t)) hm k j i r (Ne.symm hjk) (Ne.symm hik) hkr
      (Ne.symm hij) hjr hir h₂' h₁' h₄' h₃' hd₁' hd₂ hs' ?_ ?_
    · simpa only [he] using hk.comp φ hφ.tendsto_atTop
    · simpa only [he] using hj.comp φ hφ.tendsto_atTop

theorem w_quadrilateral_three_covers_impossible (hm : AdmissibleMasses mass)
    (i j k r : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hir : i ≠ r)
    (hjk : j ≠ k) (hjr : j ≠ r) (hkr : k ≠ r)
    (h₁ : l.w.force i j ≠ 0) (h₂ : l.w.force j k ≠ 0)
    (h₃ : l.w.force k r ≠ 0) (h₄ : l.w.force r i ≠ 0)
    (hd₁ : l.w.force i k = 0) (hd₂ : l.w.force j r = 0)
    (hi : MaximalTermCover (fun a t => (q t).zEquationTerm i a) {i, j, k, r})
    (hj : MaximalTermCover (fun a t => (q t).zEquationTerm j a) {i, j, k, r})
    (hk : MaximalTermCover (fun a t => (q t).zEquationTerm k a) {i, j, k, r}) :
    False :=
  (l.swapBalanced hb).z_quadrilateral_three_covers_impossible (fun t => (hb t).symm)
    hm i j k r hij hik hir hjk hjr hkr h₁ h₂ h₃ h₄ hd₁ hd₂ hi hj hk

end ScaledZWLimit
end CentralConfigurations
