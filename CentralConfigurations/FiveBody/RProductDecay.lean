import CentralConfigurations.FiveBody.RZeroCard
import CentralConfigurations.FiveBody.FixedLevelFiniteness
import Mathlib.Analysis.Asymptotics.Lemmas

/-! The complete R product decays at D5, including the sharp six-factor
case. Only the supplied metric orders are inputs; their actual D5 proof
is a separate module. -/

namespace CentralConfigurations.FiveBody.RZero
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators

theorem finite_product_isLittleO (R : Finset (Fin 10)) (U : Fin 10)
    (hU : U ∈ R) (hcard : R.card ≤ 6)
    {α : Type*} (l : Filter α) (eps : α → ℝ) (Q : α → Fin 10 → ℂ)
    (hne : ∀ᶠ t in l, eps t ≠ 0)
    (hin : (fun t => Q t U) =o[l] (fun t => eps t ^ 5))
    (hout : ∀ e ∈ R, e ≠ U → (fun t => Q t e) =o[l] (fun t => (eps t)⁻¹)) :
    (fun t => ∏ e ∈ R, Q t e) =o[l] (fun t => eps t ^ (6 - R.card)) := by
  classical
  have herase : ∀ e ∈ R.erase U,
      (fun t => Q t e) =O[l] (fun t => (eps t)⁻¹) := by
    intro e he
    exact (hout e (Finset.mem_erase.mp he).2 (Finset.mem_erase.mp he).1).isBigO
  have hp := hin.mul_isBigO (IsBigO.finsetProd herase)
  have hn : (R.erase U).card ≤ 5 := by
    have hc := Finset.card_erase_add_one hU
    omega
  have hexp : 5 - (R.erase U).card = 6 - R.card := by
    have hc := Finset.card_erase_add_one hU
    omega
  apply hp.congr'
  · exact Eventually.of_forall (fun t => Finset.mul_prod_erase R (fun e => Q t e) hU)
  · filter_upwards [hne] with t ht
    change eps t ^ 5 * (∏ e ∈ R.erase U, (eps t)⁻¹) = eps t ^ (6 - R.card)
    rw [Finset.prod_const, inv_pow, ← pow_sub₀ (eps t) ht hn, hexp]

theorem finite_product_tendsto_zero (R : Finset (Fin 10)) (U : Fin 10)
    (hU : U ∈ R) (hcard : R.card ≤ 6)
    {α : Type*} (l : Filter α) (eps : α → ℝ) (Q : α → Fin 10 → ℂ)
    (hne : ∀ᶠ t in l, eps t ≠ 0) (heps : Tendsto eps l (𝓝 0))
    (hin : (fun t => Q t U) =o[l] (fun t => eps t ^ 5))
    (hout : ∀ e ∈ R, e ≠ U → (fun t => Q t e) =o[l] (fun t => (eps t)⁻¹)) :
    Tendsto (fun t => ∏ e ∈ R, Q t e) l (𝓝 0) :=
  (finite_product_isLittleO R U hU hcard l eps Q hne hin hout).tendsto_zero_of_tendsto
    (heps.pow (6 - R.card))

theorem completeRProduct_isLittleO (mass : Fin 5 → ℝ) (hm : ∀ i, 0 < mass i)
    (U : Fin 10) (hU : U ∈ completeR mass)
    {α : Type*} (l : Filter α) (eps : α → ℝ) (Q : α → Fin 10 → ℂ)
    (hne : ∀ᶠ t in l, eps t ≠ 0)
    (hin : (fun t => Q t U) =o[l] (fun t => eps t ^ 5))
    (hout : ∀ e ∈ completeR mass, e ≠ U →
      (fun t => Q t e) =o[l] (fun t => (eps t)⁻¹)) :
    (fun t => ∏ e ∈ completeR mass, Q t e) =o[l]
      (fun t => eps t ^ (6 - (completeR mass).card)) :=
  finite_product_isLittleO _ U hU (completeR_card_le_six mass hm) l eps Q hne hin hout

theorem completeRProduct_tendsto_zero (mass : Fin 5 → ℝ) (hm : ∀ i, 0 < mass i)
    (U : Fin 10) (hU : U ∈ completeR mass)
    {α : Type*} (l : Filter α) (eps : α → ℝ) (Q : α → Fin 10 → ℂ)
    (hne : ∀ᶠ t in l, eps t ≠ 0) (heps : Tendsto eps l (𝓝 0))
    (hin : (fun t => Q t U) =o[l] (fun t => eps t ^ 5))
    (hout : ∀ e ∈ completeR mass, e ≠ U →
      (fun t => Q t e) =o[l] (fun t => (eps t)⁻¹)) :
    Tendsto (fun t => ∏ e ∈ completeR mass, Q t e) l (𝓝 0) :=
  finite_product_tendsto_zero _ U hU (completeR_card_le_six mass hm)
    l eps Q hne heps hin hout

theorem selectedProduct_tendsto_zero_of_d5_orders
    (mass : Fin 5 → ℝ) (hm : ∀ i, 0 < mass i)
    (q : ℕ → NormalizedSystem ℂ 5 (fun i => (mass i : ℂ)))
    (eps : ℕ → ℝ) (heps_pos : ∀ t, 0 < eps t) (heps : Tendsto eps atTop (𝓝 0))
    (U : Fin 10) (hU : U ∈ completeR mass)
    (hin : (fun t => (q t).fiveBodyFourProduct U) =o[atTop] (fun t => eps t ^ 5))
    (hout : ∀ e ∈ completeR mass, e ≠ U →
      (fun t => (q t).fiveBodyFourProduct e) =o[atTop] (fun t => (eps t)⁻¹)) :
    Tendsto (fun t => (q t).fiveBodySelectedProduct (completeR mass)) atTop (𝓝 0) :=
  completeRProduct_tendsto_zero mass hm U hU atTop eps
    (fun t e => (q t).fiveBodyFourProduct e)
    (Eventually.of_forall (fun t => ne_of_gt (heps_pos t))) heps hin hout

end
end CentralConfigurations.FiveBody.RZero
