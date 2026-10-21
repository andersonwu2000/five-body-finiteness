import CentralConfigurations.Asymptotics.TorqueLimits

/-!
# The dominant inverse-distance ratio from the two-source torque equation

This is the finite-sum cancellation step in Albouy--Kaloshin, Proposition 4.
Its limit hypotheses will be supplied by the actual trace-two diagram. The
inverse-distance ratio itself is obtained from torque, so no root sign is chosen.
-/

namespace CentralConfigurations

open Filter Asymptotics
open scoped Topology BigOperators

theorem pair_torque_ratio_limit {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hmj : mass j ≠ 0) (hmk : mass k ≠ 0)
    (hci : ∀ r, r ≠ i → r ≠ j →
      Tendsto (fun t => (q t).torqueCorrection i r) atTop (𝓝 (-1)))
    (hcj : ∀ r, r ≠ i → r ≠ j →
      Tendsto (fun t => (q t).torqueCorrection j r) atTop (𝓝 (-1)))
    (hdi : ∀ r, r ≠ i → r ≠ j → r ≠ k →
      Tendsto (fun t => (q t).delta i r / (q t).delta i k) atTop (𝓝 0))
    (hdj : ∀ r, r ≠ i → r ≠ j → r ≠ k →
      Tendsto (fun t => (q t).delta j r / (q t).delta i k) atTop (𝓝 0)) :
    Tendsto (fun t => (q t).delta j k / (q t).delta i k) atTop (𝓝 (-mass i / mass j)) := by
  classical
  let s : Finset (Fin n) := ({i, j} : Finset (Fin n))ᶜ
  have hs : ∀ r, r ∈ s ↔ r ≠ i ∧ r ≠ j := by
    intro r
    simp [s]
  have hk : k ∈ s := (hs k).mpr ⟨hik.symm, hjk.symm⟩
  have hd (t : ℕ) : (q t).delta i k ≠ 0 := by
    intro hz
    have heq := (q t).distance i k hik
    simp [hz] at heq
  let f : Fin n → ℕ → ℂ := fun r t =>
    mass i * mass r * ((q t).delta i r / (q t).delta i k) * (q t).torqueCorrection i r +
    mass j * mass r * ((q t).delta j r / (q t).delta i k) * (q t).torqueCorrection j r
  have hsum (t : ℕ) : (∑ r ∈ s, f r t) = 0 := by
    calc
      _ = (∑ r ∈ s, (mass i * mass r * (q t).torqueTerm i r +
          mass j * mass r * (q t).torqueTerm j r)) / (q t).delta i k := by
        rw [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r _
        dsimp [f]
        rw [(q t).torqueTerm_eq i r, (q t).torqueTerm_eq j r]
        simp only [div_eq_mul_inv]
        ring
      _ = 0 := by rw [(q t).pair_torque_zero i j hij, zero_div]
  let rest : ℕ → ℂ := fun t => ∑ r ∈ s.erase k, f r t
  have hrest : Tendsto rest atTop (𝓝 0) := by
    have h : Tendsto (fun t => ∑ r ∈ s.erase k, f r t) atTop
        (𝓝 (∑ r ∈ s.erase k, (0 : ℂ))) := tendsto_finsetSum (s.erase k) (fun r hr => by
      have hrk := (Finset.mem_erase.mp hr).1
      have hrs := (hs r).mp (Finset.mem_erase.mp hr).2
      have hi := ((hdi r hrs.1 hrs.2 hrk).const_mul (mass i * mass r)).mul (hci r hrs.1 hrs.2)
      have hj := ((hdj r hrs.1 hrs.2 hrk).const_mul (mass j * mass r)).mul (hcj r hrs.1 hrs.2)
      exact (show Tendsto (f r) atTop (𝓝 0) from by
        simpa only [mul_zero, zero_mul, add_zero] using hi.add hj))
    simpa only [Finset.sum_const_zero] using h
  let c : ℕ → ℂ := fun t => mass j * mass k * (q t).torqueCorrection j k
  let e : ℕ → ℂ := fun t => (q t).delta j k / (q t).delta i k
  have heq (t : ℕ) : e t * c t =
      -(mass i * mass k * (q t).torqueCorrection i k) - rest t := by
    have hh := Finset.sum_erase_add s (fun r => f r t) hk
    rw [hsum t] at hh
    change rest t + f k t = 0 at hh
    dsimp [f] at hh
    rw [div_self (hd t), mul_one] at hh
    dsimp [e, c]
    linear_combination hh
  have hnum : Tendsto (fun t => -(mass i * mass k * (q t).torqueCorrection i k) - rest t)
      atTop (𝓝 (mass i * mass k)) := by
    have h := ((hci k hik.symm hjk.symm).const_mul (mass i * mass k)).neg.sub hrest
    simpa only [mul_neg_one, neg_neg, sub_zero] using h
  have hprod : Tendsto (fun t => e t * c t) atTop (𝓝 (mass i * mass k)) := by
    simpa only [heq] using hnum
  have hc : Tendsto c atTop (𝓝 (mass j * mass k * (-1))) :=
    tendsto_const_nhds.mul (hcj k hik.symm hjk.symm)
  have hcn : mass j * mass k * (-1 : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero hmj hmk) (by norm_num)
  apply (tendsto_mul_iff_of_ne_zero hc hcn).mp
  convert hprod using 1
  congr 1
  field_simp [hmj]

end CentralConfigurations
