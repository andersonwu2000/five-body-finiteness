import CentralConfigurations.Asymptotics.SequenceOrders
import CentralConfigurations.Model.ZWMassCenter

/-!
# The origin belongs to a uniquely close coordinate pair

Chang (2023), Proposition 2.7, following Albouy--Kaloshin (2012),
Proposition 1. The proof uses the actual force equations and the mass center.
Squared force identities retain the inverse-distance branch, so no complex
square root is chosen. Nonzero endpoint mass and nonzero total mass are explicit.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter Asymptotics

namespace ZWSystem

variable {n : ℕ} {mass : Fin n → ℂ}

theorem zForce_sq_eq_inverse (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) :
    q.zForce i j ^ 2 = ((q.z i - q.z j) * (q.w i - q.w j) ^ 3)⁻¹ := by
  have hn := mul_ne_zero (q.z_separation_ne_zero hij)
    (pow_ne_zero 3 (q.w_separation_ne_zero hij))
  apply mul_right_cancel₀ hn
  rw [inv_mul_cancel₀ hn]
  calc
    _ = (q.delta i j ^ 2 * ((q.z i - q.z j) * (q.w i - q.w j))) ^ 3 := by
      unfold zForce
      ring
    _ = 1 := by rw [q.distance i j hij]; norm_num

theorem wForce_sq_eq_inverse (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) :
    q.wForce i j ^ 2 = ((q.z i - q.z j) ^ 3 * (q.w i - q.w j))⁻¹ := by
  simpa only [swap, mul_comm] using q.swap.zForce_sq_eq_inverse i j hij

variable (q : ℕ → ZWSystem ℂ n mass)

theorem zForce_littleO_of_close_pair (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k)
    (hz : (fun t => (q t).z i - (q t).z j) =o[atTop]
      (fun t => (q t).z i - (q t).z k))
    (hw : (fun t => (q t).w i - (q t).w j) =O[atTop]
      (fun t => (q t).w i - (q t).w k)) :
    (fun t => (q t).zForce i k) =o[atTop] (fun t => (q t).zForce i j) := by
  have hp := hz.mul_isBigO (hw.pow 3)
  have hi := hp.inv_rev (Eventually.of_forall fun t he =>
    (mul_ne_zero ((q t).z_separation_ne_zero hij)
      (pow_ne_zero 3 ((q t).w_separation_ne_zero hij)) he).elim)
  have hs : (fun t => (q t).zForce i k ^ 2) =o[atTop]
      (fun t => (q t).zForce i j ^ 2) := hi.congr
    (fun t => ((q t).zForce_sq_eq_inverse i k hik).symm)
    (fun t => ((q t).zForce_sq_eq_inverse i j hij).symm)
  exact hs.of_pow (by decide : (2 : ℕ) ≠ 0)

theorem wForce_littleO_of_close_pair (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k)
    (hz : (fun t => (q t).z i - (q t).z j) =o[atTop]
      (fun t => (q t).z i - (q t).z k))
    (hw : (fun t => (q t).w i - (q t).w j) =O[atTop]
      (fun t => (q t).w i - (q t).w k)) :
    (fun t => (q t).wForce i k) =o[atTop] (fun t => (q t).wForce i j) := by
  have hp := (hz.pow (by decide : 0 < 3)).mul_isBigO hw
  have hi := hp.inv_rev (Eventually.of_forall fun t he =>
    (mul_ne_zero (pow_ne_zero 3 ((q t).z_separation_ne_zero hij))
      ((q t).w_separation_ne_zero hij) he).elim)
  have hs : (fun t => (q t).wForce i k ^ 2) =o[atTop]
      (fun t => (q t).wForce i j ^ 2) := hi.congr
    (fun t => ((q t).wForce_sq_eq_inverse i k hik).symm)
    (fun t => ((q t).wForce_sq_eq_inverse i j hij).symm)
  exact hs.of_pow (by decide : (2 : ℕ) ≠ 0)

theorem z_position_theta_dominant_force (i j : Fin n) (_hij : i ≠ j)
    (hm : mass j ≠ 0)
    (hf : ∀ k, k ≠ i → k ≠ j →
      (fun t => (q t).zForce i k) =o[atTop] (fun t => (q t).zForce i j)) :
    (fun t => (q t).z i) =Θ[atTop] (fun t => (q t).zForce i j) := by
  have hr : (fun t => ∑ k ∈ Finset.univ.erase j, mass k * (q t).zForce i k)
      =o[atTop] (fun t => (q t).zForce i j) := by
    apply IsLittleO.sum
    intro k hk
    by_cases hki : k = i
    · simp only [hki, zForce, sub_self, mul_zero]
      exact isLittleO_zero _ _
    · exact (hf k hki (Finset.mem_erase.mp hk).1).const_mul_left (mass k)
  have heq (t : ℕ) :
      (∑ k ∈ Finset.univ.erase j, mass k * (q t).zForce i k) +
        mass j * (q t).zForce i j = (q t).z i := by
    rw [Finset.sum_erase_add (s := Finset.univ)
      (f := fun k => mass k * (q t).zForce i k) (Finset.mem_univ j)]
    simpa only [zForce, mul_assoc] using ((q t).force_z i).symm
  refine ⟨?_, ?_⟩
  · exact (hr.isBigO.add (isBigO_const_mul_self (mass j)
      (fun t => (q t).zForce i j) atTop)).congr heq (fun _ => rfl)
  · exact (isBigO_self_const_mul hm (fun t => (q t).zForce i j) atTop).trans
      (((hr.const_mul_right hm).right_isBigO_add).congr (fun _ => rfl) heq)

theorem w_position_theta_dominant_force (i j : Fin n) (hij : i ≠ j)
    (hm : mass j ≠ 0)
    (hf : ∀ k, k ≠ i → k ≠ j →
      (fun t => (q t).wForce i k) =o[atTop] (fun t => (q t).wForce i j)) :
    (fun t => (q t).w i) =Θ[atTop] (fun t => (q t).wForce i j) :=
  z_position_theta_dominant_force (fun t => (q t).swap) i j hij hm hf

theorem w_position_isBigO_pair_of_row (hM : (∑ k, mass k) ≠ 0) (i j : Fin n)
    (hw : ∀ k, k ≠ i → (fun t => (q t).w i - (q t).w k) =O[atTop]
      (fun t => (q t).w i - (q t).w j)) :
    (fun t => (q t).w i) =O[atTop] (fun t => (q t).w i - (q t).w j) := by
  have hs : (fun t => ∑ k ∈ Finset.univ.erase i, mass k * ((q t).w i - (q t).w k))
      =O[atTop] (fun t => (q t).w i - (q t).w j) :=
    IsBigO.sum (fun k hk => (hw k (Finset.mem_erase.mp hk).1).const_mul_left (mass k))
  exact (isBigO_const_mul_left_iff hM).mp
    (hs.congr (fun t => (q t).mass_separation_sum_w i) (fun _ => rfl))

/-- Proposition 2.7. The same statement for the opposite color follows by swap.
The total mass condition is used at the mass center, and mass j is used at
the dominating force term. -/
theorem close_pair_contains_origin (i j : Fin n) (hij : i ≠ j)
    (hm : mass j ≠ 0) (hM : (∑ k, mass k) ≠ 0)
    (hz : ∀ k, k ≠ i → k ≠ j →
      (fun t => (q t).z i - (q t).z j) =o[atTop]
        (fun t => (q t).z i - (q t).z k))
    (hw : ∀ k, k ≠ i → k ≠ j →
      (fun t => (q t).w i - (q t).w j) =Θ[atTop]
        (fun t => (q t).w i - (q t).w k)) :
    (fun t => (q t).z i) =O[atTop] (fun t => (q t).z i - (q t).z j) ∧
    (fun t => (q t).z j) =O[atTop] (fun t => (q t).z i - (q t).z j) := by
  have hzdom := z_position_theta_dominant_force q i j hij hm
    (fun k hki hkj => zForce_littleO_of_close_pair q i j k hij hki.symm
      (hz k hki hkj) (hw k hki hkj).1)
  have hwdom := w_position_theta_dominant_force q i j hij hm
    (fun k hki hkj => wForce_littleO_of_close_pair q i j k hij hki.symm
      (hz k hki hkj) (hw k hki hkj).1)
  have hwcenter := w_position_isBigO_pair_of_row q hM i j (by
    intro k hki
    by_cases hkj : k = j
    · subst k
      exact isBigO_refl _ _
    · exact (hw k hki hkj).2)
  have hd : (fun t => (q t).delta i j ^ 3) =O[atTop] (fun _ => (1 : ℂ)) := by
    exact ((hwdom.2.trans hwcenter).mul
      (isBigO_refl (fun t => ((q t).w i - (q t).w j)⁻¹) atTop)).congr
      (fun t => by simp [wForce, (q t).w_separation_ne_zero hij])
      (fun t => mul_inv_cancel₀ ((q t).w_separation_ne_zero hij))
  have hzi : (fun t => (q t).z i) =O[atTop]
      (fun t => (q t).z i - (q t).z j) := hzdom.1.trans
    ((hd.mul (isBigO_refl (fun t => (q t).z i - (q t).z j) atTop)).congr
      (fun _ => rfl) (fun t => one_mul _))
  refine ⟨hzi, ?_⟩
  exact (hzi.sub (isBigO_refl (fun t => (q t).z i - (q t).z j) atTop)).congr
    (fun t => by ring) (fun _ => rfl)

theorem close_w_pair_contains_origin (i j : Fin n) (hij : i ≠ j)
    (hm : mass j ≠ 0) (hM : (∑ k, mass k) ≠ 0)
    (hw : ∀ k, k ≠ i → k ≠ j →
      (fun t => (q t).w i - (q t).w j) =o[atTop]
        (fun t => (q t).w i - (q t).w k))
    (hz : ∀ k, k ≠ i → k ≠ j →
      (fun t => (q t).z i - (q t).z j) =Θ[atTop]
        (fun t => (q t).z i - (q t).z k)) :
    (fun t => (q t).w i) =O[atTop] (fun t => (q t).w i - (q t).w j) ∧
    (fun t => (q t).w j) =O[atTop] (fun t => (q t).w i - (q t).w j) :=
  close_pair_contains_origin (fun t => (q t).swap) i j hij hm hM hw hz

end ZWSystem
end CentralConfigurations
