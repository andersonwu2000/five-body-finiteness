import CentralConfigurations.Diagrams.SkewPaths
import CentralConfigurations.Enumeration.MaximalTermFilters

/-!
# Proposition 4.15 for certified maximal-term covers

A nonclosed two-stroke path forbids an opposite-color middle row supported
on its two endpoints. It also forbids all three opposite-color rows from
being supported inside the path. Arbitrary certified covers are allowed;
retained terms are not assumed to be mutually comparable or truly maximal.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter Asymptotics

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem z_path_middle_pair_impossible (hm : AdmissibleMasses mass) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : l.z.force i j ≠ 0) (h₂ : l.z.force j k ≠ 0) (h₃ : l.z.force i k = 0)
    (hM : MaximalTermCover (fun a t => (q t).wEquationTerm j a) {i, k}) : False := by
  have hmi : mass i ≠ 0 := by simpa using hm {i} (Finset.singleton_nonempty i)
  have hmk : mass k ≠ 0 := by simpa using hm {k} (Finset.singleton_nonempty k)
  have h := hM.pair_isTheta hik (fun t => (q t).wEquationTerm_sum j)
  simp only [ZWSystem.wEquationTerm, if_neg hij, if_neg (Ne.symm hjk)] at h
  have hf : (fun t => (q t).wForce j i) =Θ[atTop] (fun t => (q t).wForce j k) :=
    (isTheta_const_mul_left hmi).mp ((isTheta_const_mul_right hmk).mp h)
  have he : (fun t => (q t).wForce i j) =Θ[atTop] (fun t => (q t).wForce j i) := by
    apply IsTheta.of_norm_eventuallyEq_norm (Eventually.of_forall fun t => ?_)
    change ‖(q t).swap.zForce i j‖ = ‖(q t).swap.zForce j i‖
    rw [(q t).swap.zForce_antisymm j i, norm_neg]
  exact l.z_path_opposite_forces_not_theta hb i j k hij hjk hik h₁ h₂ h₃ (he.trans hf)

/-- The smaller first separation forces both endpoint rows onto their shared
pair. Their distance would have order one, contradicting that smallness. -/
theorem smaller_z_path_pair_not_closed (hm : AdmissibleMasses mass) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (h₁ : l.z.force i j ≠ 0)
    (hz : (fun t => (q t).z i - (q t).z j) =o[atTop]
      (fun t => (q t).z j - (q t).z k))
    (hi : MaximalTermCover (fun a t => (q t).wEquationTerm i a) {i, j, k})
    (hj : MaximalTermCover (fun a t => (q t).wEquationTerm j a) {i, j, k}) : False := by
  let p := ZWSystem.pairEstimateData q hb i j hij
  let r := ZWSystem.pairEstimateData q hb j k hjk
  let s := ZWSystem.pairEstimateData q hb i k hik
  have he (t : ℕ) : p.z t + r.z t = s.z t := by
    change ((q t).z i - (q t).z j) + ((q t).z j - (q t).z k) = (q t).z i - (q t).z k
    ring
  have hzs : r.z =Θ[atTop] s.z :=
    ⟨hz.right_isBigO_add.congr_right he,
      (hz.isBigO.add (isBigO_refl r.z atTop)).congr_left he⟩
  have hwjk := l.wForce_littleO_of_z_separation_stroke hb j k i j hjk hij h₁ hz
  have hwik := l.wForce_littleO_of_z_separation_stroke hb i k i j hik hij h₁
    (hz.trans_isTheta hzs)
  have hmi : mass i ≠ 0 := by simpa using hm {i} (Finset.singleton_nonempty i)
  have hmj : mass j ≠ 0 := by simpa using hm {j} (Finset.singleton_nonempty j)
  have hti : (fun t => (q t).wEquationTerm i k) =o[atTop]
      (fun t => (q t).wEquationTerm i j) := by
    simpa only [ZWSystem.wEquationTerm, if_neg (Ne.symm hik), if_neg (Ne.symm hij)] using
      (hwik.const_mul_left (mass k)).const_mul_right hmj
  have hwji : (fun t => (q t).wForce j k) =o[atTop] (fun t => (q t).wForce j i) :=
    hwjk.neg_right.congr_right (fun t => ((q t).swap.zForce_antisymm j i).symm)
  have htj : (fun t => (q t).wEquationTerm j k) =o[atTop]
      (fun t => (q t).wEquationTerm j i) := by
    simpa only [ZWSystem.wEquationTerm, if_neg (Ne.symm hjk), if_neg hij] using
      (hwji.const_mul_left (mass k)).const_mul_right hmi
  have herase : ({i, j, k} : Finset (Fin n)).erase k = {i, j} := by
    ext a
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    aesop
  have hi' : MaximalTermCover (fun a t => (q t).wEquationTerm i a) {i, j} := by
    simpa only [herase] using hi.erase_of_littleO hti
  have hj' : MaximalTermCover (fun a t => (q t).wEquationTerm j a) {i, j} := by
    simpa only [herase] using hj.erase_of_littleO htj
  have hr := ZWSystem.two_w_pair_covers_radius_theta_one q hm i j hij hi' hj'
  have hp := (l.pair_z_stroke_iff hb i j hij).mpr h₁
  have hlarge := (p.stroke_radius_iff_z_maximal hp).mp hr
  have hsmall : p.z =o[atTop] p.scale := hz.trans_isBigO r.z_upper
  exact isLittleO_irrefl (Eventually.of_forall p.z_ne_zero).frequently
    (hsmall.trans_isTheta hlarge.symm)

theorem z_path_three_covers_impossible (hm : AdmissibleMasses mass) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : l.z.force i j ≠ 0) (h₂ : l.z.force j k ≠ 0) (h₃ : l.z.force i k = 0)
    (hi : MaximalTermCover (fun a t => (q t).wEquationTerm i a) {i, j, k})
    (hj : MaximalTermCover (fun a t => (q t).wEquationTerm j a) {i, j, k})
    (hk : MaximalTermCover (fun a t => (q t).wEquationTerm k a) {i, j, k}) : False := by
  obtain ⟨φ, hφ, hsmall | hsmall⟩ := l.z_path_skew_subsequence hb i j k hij hjk hik h₁ h₂ h₃
  · exact (l.comp φ hφ.tendsto_atTop).smaller_z_path_pair_not_closed (fun t => hb (φ t))
      hm i j k hij hjk hik h₁ hsmall (hi.comp φ hφ.tendsto_atTop) (hj.comp φ hφ.tendsto_atTop)
  · have he : ({k, j, i} : Finset (Fin n)) = {i, j, k} := by
      ext a
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    have hs : (fun t => (q (φ t)).z k - (q (φ t)).z j) =o[atTop]
        (fun t => (q (φ t)).z j - (q (φ t)).z i) := by
      exact hsmall.neg_left.neg_right.congr
        (fun t => by ring) (fun t => by ring)
    refine (l.comp φ hφ.tendsto_atTop).smaller_z_path_pair_not_closed (fun t => hb (φ t))
      hm k j i (Ne.symm hjk) (Ne.symm hij) (Ne.symm hik) ?_ hs ?_ ?_
    · change l.z.force k j ≠ 0
      rw [l.z.antisymm k j]
      exact neg_ne_zero.mpr h₂
    · simpa only [he] using hk.comp φ hφ.tendsto_atTop
    · simpa only [he] using hj.comp φ hφ.tendsto_atTop

/-- Both conclusions of Proposition 4.15(a). -/
theorem z_path_maximal_covers (hm : AdmissibleMasses mass)
    (M : Fin n → Finset (Fin n))
    (hM : ∀ p, MaximalTermCover (fun a t => (q t).wEquationTerm p a) (M p))
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : l.z.force i j ≠ 0) (h₂ : l.z.force j k ≠ 0) (h₃ : l.z.force i k = 0) :
    M j ≠ {i, k} ∧ ∃ p ∈ ({i, j, k} : Finset (Fin n)), ¬ M p ⊆ {i, j, k} := by
  constructor
  · intro he
    have hj := hM j
    rw [he] at hj
    exact l.z_path_middle_pair_impossible hb hm i j k hij hjk hik h₁ h₂ h₃ hj
  · by_contra hn
    have hsub (p) (hp : p ∈ ({i, j, k} : Finset (Fin n))) : M p ⊆ {i, j, k} := by
      by_contra h
      exact hn ⟨p, hp, h⟩
    exact l.z_path_three_covers_impossible hb hm i j k hij hjk hik h₁ h₂ h₃
      ((hM i).mono (hsub i (by simp))) ((hM j).mono (hsub j (by simp)))
      ((hM k).mono (hsub k (by simp)))

/-- Proposition 4.15(b), by exchanging the two colors of the same sequence. -/
theorem w_path_maximal_covers (hm : AdmissibleMasses mass)
    (M : Fin n → Finset (Fin n))
    (hM : ∀ p, MaximalTermCover (fun a t => (q t).zEquationTerm p a) (M p))
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : l.w.force i j ≠ 0) (h₂ : l.w.force j k ≠ 0) (h₃ : l.w.force i k = 0) :
    M j ≠ {i, k} ∧ ∃ p ∈ ({i, j, k} : Finset (Fin n)), ¬ M p ⊆ {i, j, k} :=
  (l.swapBalanced hb).z_path_maximal_covers (fun t => (hb t).symm) hm M hM
    i j k hij hjk hik h₁ h₂ h₃

end ScaledZWLimit
end CentralConfigurations
