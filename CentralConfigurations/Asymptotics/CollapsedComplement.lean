import CentralConfigurations.Asymptotics.RemoteBodyOrders
import CentralConfigurations.Asymptotics.ClusterOrigin

/-!
# Distance bounds outside a collapsing complete cluster

This is the force-equation step in the distance argument of
Albouy--Kaloshin, Section 6.1 (used by Chang, Section 10.8).
The complement of one body has nonzero total mass and coordinate diameter
O(epsilon). It cannot be remote from every body of that cluster. A bounded
distance then controls every other squared distance by O(epsilon^{-1}).
-/

namespace CentralConfigurations
noncomputable section
open scoped BigOperators Topology
open Filter Asymptotics

namespace ZWSystem
variable {n : ℕ} {mass : Fin n → ℂ}

theorem remote_complement_z_separation_small (q : ℕ → ZWSystem ℂ n mass)
    (eps : ℕ → ℂ) (i j : Fin n) (_hji : j ≠ i)
    (hC : (∑ k ∈ Finset.univ.erase i, mass k) ≠ 0)
    (hd : ∀ k, k ≠ i → (fun t => (q t).delta i k) =o[atTop] (fun _ => (1 : ℂ)))
    (hz : ∀ k, k ≠ i → (fun t => (q t).z j - (q t).z k) =O[atTop] eps) :
    (fun t => (q t).z i - (q t).z j) =O[atTop] eps := by
  classical
  let S : Finset (Fin n) := Finset.univ.erase i
  let M := ∑ k, mass k
  let C := ∑ k ∈ S, mass k
  let f := fun t => (q t).z i - (q t).z j
  let d := fun t => ∑ k ∈ S, mass k * (q t).delta i k ^ 3
  let g := fun t => ∑ k ∈ S, mass k * (q t).delta i k ^ 3 * ((q t).z j - (q t).z k)
  let b := fun t => ∑ k ∈ S, mass k * ((q t).z j - (q t).z k)
  have hd0 : Tendsto d atTop (𝓝 0) := by
    have ho : d =o[atTop] (fun _ => (1 : ℂ)) := by
      apply IsLittleO.sum
      intro k hk
      simpa only [one_pow] using
        ((hd k (Finset.mem_erase.mp hk).1).pow (by decide : 0 < 3)).const_mul_left (mass k)
    exact (isLittleO_one_iff ℂ).mp ho
  have hg : g =O[atTop] eps := by
    apply IsBigO.sum
    intro k hk
    have hc := ((hd k (Finset.mem_erase.mp hk).1).pow (by decide : 0 < 3)).isBigO.const_mul_left (mass k)
    simpa only [one_pow,one_mul] using hc.mul (hz k (Finset.mem_erase.mp hk).1)
  have hb : b =O[atTop] eps := by
    apply IsBigO.sum
    intro k hk
    exact (hz k (Finset.mem_erase.mp hk).1).const_mul_left (mass k)
  have hforce (t) : (q t).z i = d t * f t + g t := by
    rw [(q t).force_z i]
    have hs := Finset.sum_erase_add (s := Finset.univ)
      (f := fun k => mass k * (q t).delta i k ^ 3 * ((q t).z i - (q t).z k)) (Finset.mem_univ i)
    simp only [sub_self,mul_zero,add_zero] at hs
    rw [← hs]
    dsimp [d,f,g,S]
    rw [Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hcenter (t) : M * (q t).z i = C * f t + b t := by
    rw [show M * (q t).z i = ∑ k ∈ S, mass k * ((q t).z i - (q t).z k) from
      ((q t).mass_separation_sum_z i).symm]
    dsimp [C,f,b]
    rw [Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have heq (t) : (C - M * d t) * f t = M * g t - b t := by
    linear_combination -(hcenter t) + M * (hforce t)
  have hcoef : Tendsto (fun t => C - M * d t) atTop (𝓝 C) := by
    simpa only [mul_zero,sub_zero] using tendsto_const_nhds.sub (tendsto_const_nhds.mul hd0)
  have hne : ∀ᶠ t in atTop, C - M * d t ≠ 0 := hcoef.eventually (eventually_ne_nhds hC)
  have hi : (fun t => (C - M * d t)⁻¹) =O[atTop] (fun _ => (1 : ℂ)) :=
    (hcoef.inv₀ hC).isBigO_one ℂ
  have hh := hi.mul ((hg.const_mul_left M).sub hb)
  have hh' : (fun t => (C - M * d t)⁻¹ * (M * g t - b t)) =O[atTop] eps := by
    simpa only [one_mul] using hh
  apply hh'.congr' _ (Eventually.of_forall fun _ => rfl)
  filter_upwards [hne] with t ht
  rw [← heq t,← mul_assoc,inv_mul_cancel₀ ht,one_mul]

theorem remote_complement_w_separation_small (q : ℕ → ZWSystem ℂ n mass)
    (eps : ℕ → ℂ) (i j : Fin n) (hji : j ≠ i)
    (hC : (∑ k ∈ Finset.univ.erase i, mass k) ≠ 0)
    (hd : ∀ k, k ≠ i → (fun t => (q t).delta i k) =o[atTop] (fun _ => (1 : ℂ)))
    (hw : ∀ k, k ≠ i → (fun t => (q t).w j - (q t).w k) =O[atTop] eps) :
    (fun t => (q t).w i - (q t).w j) =O[atTop] eps :=
  remote_complement_z_separation_small (fun t => (q t).swap) eps i j hji hC hd hw

theorem collapsing_complement_not_all_remote (q : ℕ → ZWSystem ℂ n mass)
    (eps : ℕ → ℂ) (heps : Tendsto eps atTop (𝓝 0)) (i j : Fin n) (hji : j ≠ i)
    (hC : (∑ k ∈ Finset.univ.erase i, mass k) ≠ 0)
    (hz : ∀ k, k ≠ i → (fun t => (q t).z j - (q t).z k) =O[atTop] eps)
    (hw : ∀ k, k ≠ i → (fun t => (q t).w j - (q t).w k) =O[atTop] eps) :
    ¬ ∀ k, k ≠ i → (fun t => (q t).delta i k) =o[atTop] (fun _ => (1 : ℂ)) := by
  intro hd
  have hz0 := (remote_complement_z_separation_small q eps i j hji hC hd hz).trans_isLittleO
    ((isLittleO_one_iff ℂ).mpr heps)
  have hw0 := (remote_complement_w_separation_small q eps i j hji hC hd hw).trans_isLittleO
    ((isLittleO_one_iff ℂ).mpr heps)
  have hz0 := (isLittleO_one_iff ℂ).mp hz0
  have hw0 := (isLittleO_one_iff ℂ).mp hw0
  have hd0 := (isLittleO_one_iff ℂ).mp (hd j hji)
  have h := (hd0.pow 2).mul (hz0.mul hw0)
  simp only [zero_pow (by decide : 2 ≠ 0),zero_mul] at h
  have hc : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 0) :=
    h.congr (fun t => (q t).distance i j hji.symm)
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hc)

end ZWSystem

namespace SequenceOrderAssignment
variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
include o

theorem collapsing_complement_has_bounded_radius (i j : Fin n) (hji : j ≠ i)
    (hC : (∑ k ∈ Finset.univ.erase i, mass k) ≠ 0)
    (hz : ∀ k, k ≠ i → (fun t => (q t).z j - (q t).z k) =O[atTop]
      (fun t => ((q t).epsilon : ℂ)))
    (hw : ∀ k, k ≠ i → (fun t => (q t).w j - (q t).w k) =O[atTop]
      (fun t => ((q t).epsilon : ℂ))) :
    ∃ k, k ≠ i ∧ (fun t => ((q t).delta i k)⁻¹) =O[atTop] (fun _ => (1 : ℂ)) := by
  have hex : ∃ k, k ≠ i ∧ o.radius i k ≤ 3 := by
    by_contra hn
    push Not at hn
    apply ZWSystem.collapsing_complement_not_all_remote q _
      (ZWSystem.epsilon_tendsto_zero_of_inverseScale q ha) i j hji hC hz hw
    intro k hk
    exact o.delta_littleO_one_of_radius_gt_three i k (hn k hk)
  obtain ⟨k,hki,hk⟩ := hex
  exact ⟨k,hki,(o.radius_level i k).le_three_iff_isBigO_middle.mp hk⟩

theorem collapsing_complement_squared_radius_bound
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j : Fin n) (hji : j ≠ i)
    (hC : (∑ k ∈ Finset.univ.erase i, mass k) ≠ 0)
    (hz : ∀ a b, a ≠ i → b ≠ i → (fun t => (q t).z a - (q t).z b) =O[atTop]
      (fun t => ((q t).epsilon : ℂ)))
    (hw : ∀ a b, a ≠ i → b ≠ i → (fun t => (q t).w a - (q t).w b) =O[atTop]
      (fun t => ((q t).epsilon : ℂ)))
    (k : Fin n) (hki : k ≠ i) :
    (fun t => ((q t).delta i k)⁻¹ ^ 2) =O[atTop]
      (fun t => (((q t).epsilon : ℂ))⁻¹) := by
  let eps := fun t => ((q t).epsilon : ℂ)
  have heps0 : Tendsto eps atTop (𝓝 0) := ZWSystem.epsilon_tendsto_zero_of_inverseScale q ha
  have hepsn (t) : eps t ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt ((q t).epsilon_pos i₀ j₀ hij₀))
  have heps : eps =O[atTop] (fun _ => (1 : ℂ)) := heps0.isBigO_one ℂ
  have hone : (fun _ : ℕ => (1 : ℂ)) =O[atTop] (fun t => (eps t)⁻¹) := by
    simpa only [inv_one] using heps.inv_rev (Eventually.of_forall fun t ht => (hepsn t ht).elim)
  obtain ⟨b,hbi,hr⟩ := o.collapsing_complement_has_bounded_radius i j hji hC
    (fun k hk => hz j k hji hk) (fun k hk => hw j k hji hk)
  let p := ZWSystem.pairEstimateData q hb i b hbi.symm
  have hbase : (fun t => ((q t).z i - (q t).z b) * ((q t).w i - (q t).w b))
      =O[atTop] (fun t => (eps t)⁻¹) := by
    have h := (hr.pow 2).congr (fun t => p.radius_sq t) (fun _ => one_pow 2)
    exact h.trans hone
  have hzw : (fun t => ((q t).z i - (q t).z b) * ((q t).w b - (q t).w k))
      =O[atTop] (fun t => (eps t)⁻¹) :=
    (p.z_upper.mul (hw b k hbi hki)).congr (fun _ => rfl)
      (fun t => by change (eps t)⁻¹ ^ 2 * eps t = (eps t)⁻¹; field_simp [hepsn t])
  have hwz : (fun t => ((q t).z b - (q t).z k) * ((q t).w i - (q t).w b))
      =O[atTop] (fun t => (eps t)⁻¹) :=
    ((hz b k hbi hki).mul p.w_upper).congr (fun _ => rfl)
      (fun t => by change eps t * (eps t)⁻¹ ^ 2 = (eps t)⁻¹; field_simp [hepsn t])
  have hbb : (fun t => ((q t).z b - (q t).z k) * ((q t).w b - (q t).w k))
      =O[atTop] (fun t => (eps t)⁻¹) := by
    have he2 : (fun t => eps t * eps t) =O[atTop] (fun _ => (1 : ℂ)) := by
      simpa only [one_mul] using heps.mul heps
    exact ((hz b k hbi hki).mul (hw b k hbi hki)).trans (he2.trans hone)
  let pk := ZWSystem.pairEstimateData q hb i k hki.symm
  exact (((hbase.add hzw).add hwz).add hbb).congr
    (fun t => by
      calc
        _ = ((q t).z i - (q t).z k) * ((q t).w i - (q t).w k) := by ring
        _ = _ := (pk.radius_sq t).symm)
    (fun _ => rfl)

end SequenceOrderAssignment
end
end CentralConfigurations
