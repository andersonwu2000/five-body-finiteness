import CentralConfigurations.Diagrams.QuadrilateralMaximalOrders

/-!
# The external pair in Section 11.7, diagram 59

The proof works with certified covers, not hypothetical exact maximal sets.
After one finite simultaneous comparison extraction, if a row cannot discard
the external pair, every other quadrilateral row can discard it. Thus at
least three rows are closed, giving the proved quadrilateral contradiction.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

namespace PairEstimateData

theorem z_cube_from_opposite_force (p : PairEstimateData) (t : ℕ) :
    (p.wForce t)⁻¹ ^ 2 * (p.w t)⁻¹ = p.z t ^ 3 := by
  have h : p.wForce t ^ 2 = (p.w t * p.z t ^ 3)⁻¹ := p.swap.zForce_sq_inverse t
  rw [inv_pow, h, inv_inv]
  field_simp [p.w_ne_zero t]

theorem z_littleO_of_wForce_bigO (p r : PairEstimateData)
    (hf : p.wForce =O[atTop] r.wForce) (hw : p.w =o[atTop] r.w) :
    r.z =o[atTop] p.z := by
  have hf' := hf.inv_rev (Eventually.of_forall fun t he => (p.wForce_ne_zero t he).elim)
  have hw' := hw.inv_rev (Eventually.of_forall fun t he => (p.w_ne_zero t he).elim)
  have hp := (hf'.pow 2).mul_isLittleO hw'
  have hs : (fun t => r.z t ^ 3) =o[atTop] (fun t => p.z t ^ 3) :=
    hp.congr (fun t => r.z_cube_from_opposite_force t) (fun t => p.z_cube_from_opposite_force t)
  exact hs.of_pow (by decide : (3 : ℕ) ≠ 0)

end PairEstimateData

namespace ZWSystem

variable {n : ℕ} {mass : Fin n → ℂ} (q : ℕ → ZWSystem ℂ n mass)
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)

include hb in
/-- A non-negligible external interaction at one row is negligible at any
other row whose internal w-separation is smaller than both external ones. -/
theorem external_w_force_transfer (p i j : Fin n)
    (hip : i ≠ p) (hjp : j ≠ p) (hij : i ≠ j)
    (hf : (fun t => (q t).wForce i j) =O[atTop] (fun t => (q t).wForce i p))
    (hwi : (fun t => (q t).w i - (q t).w j) =o[atTop]
      (fun t => (q t).w i - (q t).w p))
    (hwj : (fun t => (q t).w j - (q t).w i) =o[atTop]
      (fun t => (q t).w j - (q t).w p)) :
    (fun t => (q t).wForce j p) =o[atTop] (fun t => (q t).wForce j i) := by
  let a := pairEstimateData q hb i j hij
  let b := pairEstimateData q hb i p hip
  let c := pairEstimateData q hb j i (Ne.symm hij)
  let d := pairEstimateData q hb j p hjp
  have hz := a.z_littleO_of_wForce_bigO b hf hwi
  have hz' : (fun t => (q t).z p - (q t).z i) =o[atTop]
      (fun t => (q t).z i - (q t).z j) := hz.neg_left.congr_left (fun t => by
    change -((q t).z i - (q t).z p) = (q t).z p - (q t).z i
    ring)
  have htheta := separation_theta_of_littleO hz'
  have hcd : c.z =O[atTop] d.z := by
    change (fun t => (q t).z j - (q t).z i) =O[atTop]
      (fun t => (q t).z j - (q t).z p)
    simpa only [isBigO_iff, norm_sub_rev] using htheta.1
  exact c.wForce_littleO_of_separations d hwj.isBigO hcd (Or.inl hwj)

/-- One strict force comparison removes both comparable external terms. -/
theorem w_cover_of_small_external_pair (hm : AdmissibleMasses mass)
    (S : Finset (Fin n)) (p v i j : Fin n) (hp : p ∉ S) (hv : v ∉ S)
    (hi : i ∈ S) (hij : i ≠ j)
    (hM : MaximalTermCover (fun a t => (q t).wEquationTerm i a) (insert p (insert v S)))
    (hext : (fun t => (q t).wForce i p) =Θ[atTop] (fun t => (q t).wForce i v))
    (hs : (fun t => (q t).wForce i p) =o[atTop] (fun t => (q t).wForce i j)) :
    MaximalTermCover (fun a t => (q t).wEquationTerm i a) S := by
  have hpi : p ≠ i := by intro h; exact hp (h ▸ hi)
  have hvi : v ≠ i := by intro h; exact hv (h ▸ hi)
  have hmj : mass j ≠ 0 := by simpa using hm {j} (Finset.singleton_nonempty j)
  have hsp : (fun t => (q t).wEquationTerm i p) =o[atTop]
      (fun t => (q t).wEquationTerm i j) := by
    simpa only [wEquationTerm, if_neg hpi, if_neg (Ne.symm hij)] using
      (hs.const_mul_left (mass p)).const_mul_right hmj
  have hsv : (fun t => (q t).wEquationTerm i v) =o[atTop]
      (fun t => (q t).wEquationTerm i j) := by
    simpa only [wEquationTerm, if_neg hvi, if_neg (Ne.symm hij)] using
      ((hext.2.trans_isLittleO hs).const_mul_left (mass v)).const_mul_right hmj
  intro a ha
  by_cases hap : a = p
  · subst a; exact ⟨j, hsp⟩
  by_cases hav : a = v
  · subst a; exact ⟨j, hsv⟩
  exact hM a (by simp [hap, hav, ha])

end ZWSystem

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

set_option maxHeartbeats 0 in
/-- The external pair can obstruct at most one closed row after extraction;
the other three rows invoke the Section 11.7 quadrilateral exclusion. -/
theorem z_quadrilateral_external_pair_impossible (hm : AdmissibleMasses mass)
    (i j k r p v : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hir : i ≠ r)
    (hjk : j ≠ k) (hjr : j ≠ r) (hkr : k ≠ r)
    (h₁ : l.z.force i j ≠ 0) (h₂ : l.z.force j k ≠ 0)
    (h₃ : l.z.force k r ≠ 0) (h₄ : l.z.force r i ≠ 0)
    (hd₁ : l.z.force i k = 0) (hd₂ : l.z.force j r = 0)
    (hp : p ∉ ({i, j, k, r} : Finset (Fin n)))
    (hv : v ∉ ({i, j, k, r} : Finset (Fin n)))
    (hM : ∀ a ∈ ({i, j, k, r} : Finset (Fin n)),
      MaximalTermCover (fun b t => (q t).wEquationTerm a b) {p, v, i, j, k, r})
    (hext : ∀ a ∈ ({i, j, k, r} : Finset (Fin n)),
      (fun t => (q t).wForce a p) =Θ[atTop] (fun t => (q t).wForce a v))
    (hw : ∀ a ∈ ({i, j, k, r} : Finset (Fin n)),
      ∀ b ∈ ({i, j, k, r} : Finset (Fin n)), a ≠ b →
      (fun t => (q t).w a - (q t).w b) =o[atTop]
        (fun t => (q t).w a - (q t).w p)) : False := by
  classical
  let S : Finset (Fin n) := {i, j, k, r}
  obtain ⟨φ, hφ, ht⟩ := exists_simultaneous_order_trichotomy
    (fun a : Fin n × Fin n => fun t => (q t).wForce a.1 a.2)
    (fun a : Fin n × Fin n => fun t => if a.1 = p then (1 : ℂ) else (q t).wForce a.1 p)
    (fun a => Eventually.of_forall fun t => by
      dsimp only
      split_ifs with h
      · exact one_ne_zero
      · exact (q t).wForce_ne_zero_of_ne a.1 p h)
  let q' := fun t => q (φ t)
  let Good (a : Fin n) := MaximalTermCover (fun b t => (q' t).wEquationTerm a b) S
  have hclose (a b : Fin n) (ha : a ∈ S) (hab : a ≠ b)
      (hs : (fun t => (q' t).wForce a p) =o[atTop] (fun t => (q' t).wForce a b)) : Good a :=
    ZWSystem.w_cover_of_small_external_pair q' hm S p v a b hp hv ha hab
      ((hM a ha).comp φ hφ.tendsto_atTop)
      ⟨(hext a ha).1.comp_tendsto hφ.tendsto_atTop,
        (hext a ha).2.comp_tendsto hφ.tendsto_atTop⟩ hs
  have hothers (a b : Fin n) (ha : a ∈ S) (hb' : b ∈ S)
      (hab : a ≠ b) (hbad : ¬ Good a) : Good b := by
    have hap : a ≠ p := by intro he; exact hp (he ▸ ha)
    have hbp : b ≠ p := by intro he; exact hp (he ▸ hb')
    have ht' : (fun t => (q' t).wForce a b) =o[atTop] (fun t => (q' t).wForce a p) ∨
        (fun t => (q' t).wForce a b) =Θ[atTop] (fun t => (q' t).wForce a p) ∨
        (fun t => (q' t).wForce a p) =o[atTop] (fun t => (q' t).wForce a b) := by
      simpa only [Function.comp_def, if_neg hap] using ht (a, b)
    have hf : (fun t => (q' t).wForce a b) =O[atTop] (fun t => (q' t).wForce a p) := by
      rcases ht' with h | h | h
      · exact h.isBigO
      · exact h.1
      · exact (hbad (hclose a b ha hab h)).elim
    exact hclose b a hb' (Ne.symm hab)
      (ZWSystem.external_w_force_transfer q' (fun t => hb (φ t)) p a b hap hbp hab hf
        ((hw a ha b hb' hab).comp_tendsto hφ.tendsto_atTop)
        ((hw b hb' a ha (Ne.symm hab)).comp_tendsto hφ.tendsto_atTop))
  have hi : i ∈ S := by simp [S]
  have hj : j ∈ S := by simp [S]
  have hk : k ∈ S := by simp [S]
  have hr : r ∈ S := by simp [S]
  have hdki : l.z.force k i = 0 := by rw [l.z.antisymm k i, hd₁, neg_zero]
  have hdrj : l.z.force r j = 0 := by rw [l.z.antisymm r j, hd₂, neg_zero]
  have hrot₁ : ({j, k, r, i} : Finset (Fin n)) = S := by ext a; simp [S]; tauto
  have hrot₂ : ({k, r, i, j} : Finset (Fin n)) = S := by ext a; simp [S]; tauto
  have hrot₃ : ({r, i, j, k} : Finset (Fin n)) = S := by ext a; simp [S]; tauto
  by_cases hgi : Good i
  · by_cases hgj : Good j
    · by_cases hgk : Good k
      · exact (l.comp φ hφ.tendsto_atTop).z_quadrilateral_three_covers_impossible
          (fun t => hb (φ t)) hm i j k r hij hik hir hjk hjr hkr
          h₁ h₂ h₃ h₄ hd₁ hd₂ hgi hgj hgk
      · refine (l.comp φ hφ.tendsto_atTop).z_quadrilateral_three_covers_impossible
          (fun t => hb (φ t)) hm r i j k (Ne.symm hir) (Ne.symm hjr) (Ne.symm hkr)
          hij hik hjk h₄ h₁ h₂ h₃ hdrj hd₁ ?_ ?_ ?_
        · simpa only [hrot₃] using hothers k r hk hr hkr hgk
        · simpa only [hrot₃] using hgi
        · simpa only [hrot₃] using hgj
    · refine (l.comp φ hφ.tendsto_atTop).z_quadrilateral_three_covers_impossible
        (fun t => hb (φ t)) hm k r i j hkr (Ne.symm hik) (Ne.symm hjk)
        (Ne.symm hir) (Ne.symm hjr) hij h₃ h₄ h₁ h₂ hdki hdrj ?_ ?_ ?_
      · simpa only [hrot₂] using hothers j k hj hk hjk hgj
      · simpa only [hrot₂] using hothers j r hj hr hjr hgj
      · simpa only [hrot₂] using hgi
  · refine (l.comp φ hφ.tendsto_atTop).z_quadrilateral_three_covers_impossible
      (fun t => hb (φ t)) hm j k r i hjk hjr (Ne.symm hij)
      hkr (Ne.symm hik) (Ne.symm hir) h₂ h₃ h₄ h₁ hd₂ hdki ?_ ?_ ?_
    · simpa only [hrot₁] using hothers i j hi hj hij hgi
    · simpa only [hrot₁] using hothers i k hi hk hik hgi
    · simpa only [hrot₁] using hothers i r hi hr hir hgi

end ScaledZWLimit
end CentralConfigurations
