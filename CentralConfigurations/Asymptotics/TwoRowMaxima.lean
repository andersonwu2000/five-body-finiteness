import CentralConfigurations.Asymptotics.MaximalTermSupport

/-!
# Proposition 4.14: two rows supported on the same pair

The support hypothesis says exactly that each omitted term has a sound
strict-dominance certificate. Finite-row cancellation then supplies the
asymptotic remainders used in the printed proof. Both colors retain their
actual complex inverse-distance variables.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter Asymptotics

namespace ZWSystem

variable {n : ℕ} {mass : Fin n → ℂ}
variable (q : ℕ → ZWSystem ℂ n mass)

theorem zForce_littleO_of_pair_cover (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j)
    (hM : MaximalTermCover (fun k t => (q t).zEquationTerm i k) {i, j})
    (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
    (fun t => (q t).zForce i k) =o[atTop] (fun t => (q t).zForce i j) := by
  have h := hM.omitted_littleO_of_pair hij (fun t => (q t).zEquationTerm_sum i)
    k (by simp [hki, hkj])
  simp only [zEquationTerm, if_neg hki, if_neg hij.symm] at h
  have hmk : mass k ≠ 0 := by simpa using hm {k} (Finset.singleton_nonempty k)
  exact (isLittleO_const_mul_left_iff hmk).mp h.of_const_mul_right

/-- The analytic step in 4.14 before substituting candidate-set certificates. -/
theorem two_z_rows_radius_theta_one (i j : Fin n) (hij : i ≠ j)
    (hm : mass i + mass j ≠ 0)
    (hi : ∀ k, k ≠ i → k ≠ j → (fun t => (q t).zForce i k) =o[atTop]
      (fun t => (q t).zForce i j))
    (hj : ∀ k, k ≠ i → k ≠ j → (fun t => (q t).zForce j k) =o[atTop]
      (fun t => (q t).zForce i j)) :
    (fun t => ((q t).delta i j)⁻¹) =Θ[atTop] (fun _ => (1 : ℂ)) := by
  let ri : ℕ → ℂ := fun t => ∑ k ∈ Finset.univ.erase j, mass k * (q t).zForce i k
  let rj : ℕ → ℂ := fun t => ∑ k ∈ Finset.univ.erase i, mass k * (q t).zForce j k
  have hri : ri =o[atTop] (fun t => (q t).zForce i j) := by
    apply IsLittleO.sum
    intro k hk
    by_cases hki : k = i
    · simp only [hki, zForce, sub_self, mul_zero]
      exact isLittleO_zero _ _
    · exact (hi k hki (Finset.mem_erase.mp hk).1).const_mul_left (mass k)
  have hrj : rj =o[atTop] (fun t => (q t).zForce i j) := by
    apply IsLittleO.sum
    intro k hk
    by_cases hkj : k = j
    · simp only [hkj, zForce, sub_self, mul_zero]
      exact isLittleO_zero _ _
    · exact (hj k (Finset.mem_erase.mp hk).1 hkj).const_mul_left (mass k)
  have he (t : ℕ) : ri t - rj t + (mass i + mass j) * (q t).zForce i j =
      (q t).z i - (q t).z j := by
    have hi' : ri t + mass j * (q t).zForce i j = (q t).z i := by
      dsimp only [ri]
      rw [Finset.sum_erase_add (s := Finset.univ)
        (f := fun k => mass k * (q t).zForce i k) (Finset.mem_univ j)]
      simpa only [zForce, mul_assoc] using ((q t).force_z i).symm
    have hj' : rj t + mass i * (q t).zForce j i = (q t).z j := by
      dsimp only [rj]
      rw [Finset.sum_erase_add (s := Finset.univ)
        (f := fun k => mass k * (q t).zForce j k) (Finset.mem_univ i)]
      simpa only [zForce, mul_assoc] using ((q t).force_z j).symm
    have ha : (q t).zForce j i = -(q t).zForce i j := by
      unfold zForce
      rw [(q t).delta_symm j i]
      ring
    rw [ha] at hj'
    linear_combination hi' - hj'
  have hrem := hri.sub hrj
  have hz : (fun t => (q t).z i - (q t).z j) =Θ[atTop]
      (fun t => (q t).zForce i j) := by
    refine ⟨?_, ?_⟩
    · exact (hrem.isBigO.add (isBigO_const_mul_self (mass i + mass j)
        (fun t => (q t).zForce i j) atTop)).congr he (fun _ => rfl)
    · exact (isBigO_self_const_mul hm (fun t => (q t).zForce i j) atTop).trans
        ((hrem.const_mul_right hm).right_isBigO_add.congr (fun _ => rfl) he)
  have hd₃ : (fun t => (q t).delta i j ^ 3) =Θ[atTop] (fun _ => (1 : ℂ)) :=
    theta_congr_pointwise
      (hz.symm.mul (isTheta_rfl : (fun t => ((q t).z i - (q t).z j)⁻¹) =Θ[atTop]
        (fun t => ((q t).z i - (q t).z j)⁻¹)))
      (fun t => by simp [zForce, mul_assoc, (q t).z_separation_ne_zero hij])
      (fun t => mul_inv_cancel₀ ((q t).z_separation_ne_zero hij))
  have hd : (fun t => (q t).delta i j) =Θ[atTop] (fun _ => (1 : ℂ)) :=
    theta_of_powers (by decide : (3 : ℕ) ≠ 0) (by simpa only [one_pow] using hd₃)
  simpa only [inv_one] using hd.inv

theorem two_z_pair_covers_radius_theta_one (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j)
    (hi : MaximalTermCover (fun k t => (q t).zEquationTerm i k) {i, j})
    (hj : MaximalTermCover (fun k t => (q t).zEquationTerm j k) {i, j}) :
    (fun t => ((q t).delta i j)⁻¹) =Θ[atTop] (fun _ => (1 : ℂ)) := by
  have hmass : mass i + mass j ≠ 0 := by
    simpa [hij] using hm {i, j} (by simp)
  have hj' : MaximalTermCover (fun k t => (q t).zEquationTerm j k) {j, i} := by
    simpa only [Finset.pair_comm] using hj
  apply two_z_rows_radius_theta_one q i j hij hmass
  · exact zForce_littleO_of_pair_cover q hm i j hij hi
  · intro k hki hkj
    have h := zForce_littleO_of_pair_cover q hm j i hij.symm hj' k hkj hki
    have he (t : ℕ) : (q t).zForce j i = -(q t).zForce i j := by
      unfold zForce
      rw [(q t).delta_symm j i]
      ring
    exact (h.congr_right he).of_neg_right

theorem two_w_pair_covers_radius_theta_one (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j)
    (hi : MaximalTermCover (fun k t => (q t).wEquationTerm i k) {i, j})
    (hj : MaximalTermCover (fun k t => (q t).wEquationTerm j k) {i, j}) :
    (fun t => ((q t).delta i j)⁻¹) =Θ[atTop] (fun _ => (1 : ℂ)) :=
  two_z_pair_covers_radius_theta_one (fun t => (q t).swap) hm i j hij hi hj

end ZWSystem
end CentralConfigurations
