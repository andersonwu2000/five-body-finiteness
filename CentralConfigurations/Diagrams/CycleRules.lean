import CentralConfigurations.Diagrams.QuadrilateralRules

/-!
# Cancellation on closed walks and the pentagon rule

Chang (2023), Theorem 2.6 Rule 2d and Theorem 3.6. The proof uses finite sums
of coordinate differences. It does not assume existence of a total ordering
of all separation ratios. A permutation of the sides represents closed walks;
the source's pentagon is the five-cycle instance.
-/

namespace CentralConfigurations

open Filter Asymptotics
open scoped BigOperators

theorem permutation_separations_sum_zero {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (τ : ι ≃ ι) : (∑ i, (x i - x (τ i))) = 0 := by
  rw [Finset.sum_sub_distrib, τ.sum_comp x, sub_self]

theorem sum_zero_bigO_at_term {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ → ℂ) (g : ℕ → ℂ) (e : ι)
    (hsum : ∀ t, ∑ i, f i t = 0)
    (h : ∀ i, i ≠ e → f i =O[atTop] g) : f e =O[atTop] g := by
  have ho : (fun t => ∑ i ∈ Finset.univ.erase e, f i t) =O[atTop] g :=
    IsBigO.sum (fun i hi => h i (Finset.mem_erase.mp hi).1)
  have heq (t : ℕ) : (∑ i ∈ Finset.univ.erase e, f i t) = -(f e t) := by
    have hh := Finset.sum_erase_add Finset.univ (fun i => f i t) (Finset.mem_univ e)
    rw [hsum t] at hh
    exact eq_neg_of_add_eq_zero_left hh
  simpa only [isBigO_neg_left] using ho.congr_left heq

theorem sum_zero_littleO_at_term {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ → ℂ) (g : ℕ → ℂ) (e : ι)
    (hsum : ∀ t, ∑ i, f i t = 0)
    (h : ∀ i, i ≠ e → f i =o[atTop] g) : f e =o[atTop] g := by
  have ho : (fun t => ∑ i ∈ Finset.univ.erase e, f i t) =o[atTop] g :=
    IsLittleO.sum (fun i hi => h i (Finset.mem_erase.mp hi).1)
  have heq (t : ℕ) : (∑ i ∈ Finset.univ.erase e, f i t) = -(f e t) := by
    have hh := Finset.sum_erase_add Finset.univ (fun i => f i t) (Finset.mem_univ e)
    rw [hsum t] at hh
    exact eq_neg_of_add_eq_zero_left hh
  simpa only [isLittleO_neg_left] using ho.congr_left heq

/-- The precise cancellation fact underlying the unique-maximum exclusion
in Rule 2d. All other sides cannot be negligible relative to one nonzero side. -/
theorem sum_zero_no_unique_dominant {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ → ℂ) (e : ι) (he : ∀ t, f e t ≠ 0)
    (hsum : ∀ t, ∑ i, f i t = 0)
    (h : ∀ i, i ≠ e → f i =o[atTop] f e) : False :=
  isLittleO_irrefl (Eventually.of_forall he).frequently (sum_zero_littleO_at_term f (f e) e hsum h)

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def zOnlySides (v : ι → Fin n) (τ : ι ≃ ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun k => l.z.force (v k) (v (τ k)) ≠ 0 ∧
    l.w.force (v k) (v (τ k)) = 0)

noncomputable def wOnlySides (v : ι → Fin n) (τ : ι ≃ ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun k => l.w.force (v k) (v (τ k)) ≠ 0 ∧
    l.z.force (v k) (v (τ k)) = 0)

noncomputable def doubleSides (v : ι → Fin n) (τ : ι ≃ ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun k => l.z.force (v k) (v (τ k)) ≠ 0 ∧
    l.w.force (v k) (v (τ k)) ≠ 0)

variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem cycle_z_only_count_ne_one (v : ι → Fin n) (τ : ι ≃ ι)
    (hne : ∀ k, v k ≠ v (τ k))
    (hedge : ∀ k, l.z.force (v k) (v (τ k)) ≠ 0 ∨ l.w.force (v k) (v (τ k)) ≠ 0) :
    (l.zOnlySides v τ).card ≠ 1 := by
  classical
  intro hcard
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  have heMem : e ∈ l.zOnlySides v τ := by rw [he]; simp
  have heForce : l.z.force (v e) (v (τ e)) ≠ 0 ∧ l.w.force (v e) (v (τ e)) = 0 := by
    simpa [zOnlySides] using heMem
  let p := ZWSystem.pairEstimateData q hb (v e) (v (τ e)) (hne e)
  have hs := p.single_z_separations
    ((l.pair_z_stroke_iff hb (v e) (v (τ e)) (hne e)).mpr heForce.1)
    ((l.pair_w_absent_iff hb (v e) (v (τ e)) (hne e)).mpr heForce.2)
  have ho : p.z =O[atTop] p.eps := by
    apply sum_zero_bigO_at_term (fun k t => (q t).z (v k) - (q t).z (v (τ k))) p.eps e
      (fun t => permutation_separations_sum_zero (fun k => (q t).z (v k)) τ)
    intro k hke
    have hw : l.w.force (v k) (v (τ k)) ≠ 0 := by
      intro hw
      have hz := (hedge k).resolve_right (not_not.mpr hw)
      have hk : k ∈ l.zOnlySides v τ := by simp [zOnlySides, hz, hw]
      rw [he] at hk
      exact hke (Finset.mem_singleton.mp hk)
    exact (ZWSystem.pairEstimateData q hb (v k) (v (τ k)) (hne k)).swap.stroke_w_upper
      ((l.pair_w_stroke_iff hb (v k) (v (τ k)) (hne k)).mpr hw)
  exact hs.1.not_isBigO (Eventually.of_forall p.eps_ne_zero).frequently ho

theorem cycle_w_only_count_ne_one (v : ι → Fin n) (τ : ι ≃ ι)
    (hne : ∀ k, v k ≠ v (τ k))
    (hedge : ∀ k, l.z.force (v k) (v (τ k)) ≠ 0 ∨ l.w.force (v k) (v (τ k)) ≠ 0) :
    (l.wOnlySides v τ).card ≠ 1 :=
  (l.swapBalanced hb).cycle_z_only_count_ne_one (fun t => (hb t).symm) v τ hne
    (fun k => (hedge k).symm)

theorem cycle_double_count_ne_one_of_no_w_only (v : ι → Fin n) (τ : ι ≃ ι)
    (hne : ∀ k, v k ≠ v (τ k))
    (hedge : ∀ k, l.z.force (v k) (v (τ k)) ≠ 0 ∨ l.w.force (v k) (v (τ k)) ≠ 0)
    (hwc : (l.wOnlySides v τ).card = 0) : (l.doubleSides v τ).card ≠ 1 := by
  classical
  intro hcard
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp hcard
  have heMem : e ∈ l.doubleSides v τ := by rw [he]; simp
  have heForce : l.z.force (v e) (v (τ e)) ≠ 0 ∧ l.w.force (v e) (v (τ e)) ≠ 0 := by
    simpa [doubleSides] using heMem
  let p := ZWSystem.pairEstimateData q hb (v e) (v (τ e)) (hne e)
  have hl := p.swap.stroke_z_lower
    ((l.pair_w_stroke_iff hb (v e) (v (τ e)) (hne e)).mpr heForce.2)
  have ho : p.w =o[atTop] p.eps := by
    apply sum_zero_littleO_at_term (fun k t => (q t).w (v k) - (q t).w (v (τ k))) p.eps e
      (fun t => permutation_separations_sum_zero (fun k => (q t).w (v k)) τ)
    intro k hke
    have hw : l.w.force (v k) (v (τ k)) = 0 := by
      by_contra hw
      by_cases hz : l.z.force (v k) (v (τ k)) = 0
      · have hk : k ∈ l.wOnlySides v τ := by simp [wOnlySides, hw, hz]
        rw [Finset.card_eq_zero.mp hwc] at hk
        exact Finset.notMem_empty k hk
      · have hk : k ∈ l.doubleSides v τ := by simp [doubleSides, hz, hw]
        rw [he] at hk
        exact hke (Finset.mem_singleton.mp hk)
    have hz := (hedge k).resolve_right (not_not.mpr hw)
    exact ((ZWSystem.pairEstimateData q hb (v k) (v (τ k)) (hne k)).single_z_separations
      ((l.pair_z_stroke_iff hb (v k) (v (τ k)) (hne k)).mpr hz)
      ((l.pair_w_absent_iff hb (v k) (v (τ k)) (hne k)).mpr hw)).2
  exact ho.not_isBigO (Eventually.of_forall p.w_ne_zero).frequently hl

theorem cycle_double_count_ne_one_of_no_z_only (v : ι → Fin n) (τ : ι ≃ ι)
    (hne : ∀ k, v k ≠ v (τ k))
    (hedge : ∀ k, l.z.force (v k) (v (τ k)) ≠ 0 ∨ l.w.force (v k) (v (τ k)) ≠ 0)
    (hzc : (l.zOnlySides v τ).card = 0) : (l.doubleSides v τ).card ≠ 1 := by
  have h := (l.swapBalanced hb).cycle_double_count_ne_one_of_no_w_only (fun t => (hb t).symm)
    v τ hne (fun k => (hedge k).symm) hzc
  simpa only [doubleSides, swapBalanced, and_comm] using h

end ScaledZWLimit

def pentagonRotation : Fin 5 ≃ Fin 5 where
  toFun k := k + 1
  invFun k := k + 4
  left_inv := by decide
  right_inv := by decide

def cycleZCount {n : ℕ} (A B : Fin n → Fin n → ℕ) (v : Fin 5 → Fin n) : ℕ :=
  (Finset.univ.filter (fun k => A (v k) (v (pentagonRotation k)) = 1 ∧
    B (v k) (v (pentagonRotation k)) = 0)).card

def cycleWCount {n : ℕ} (A B : Fin n → Fin n → ℕ) (v : Fin 5 → Fin n) : ℕ :=
  (Finset.univ.filter (fun k => B (v k) (v (pentagonRotation k)) = 1 ∧
    A (v k) (v (pentagonRotation k)) = 0)).card

def cycleDoubleCount {n : ℕ} (A B : Fin n → Fin n → ℕ) (v : Fin 5 → Fin n) : ℕ :=
  (Finset.univ.filter (fun k => A (v k) (v (pentagonRotation k)) = 1 ∧
    B (v k) (v (pentagonRotation k)) = 1)).card

def PentagonMatrixRule {n : ℕ} (A B : Fin n → Fin n → ℕ) : Prop :=
  ∀ v : Fin 5 → Fin n, Function.Injective v →
    (∀ k, A (v k) (v (pentagonRotation k)) + B (v k) (v (pentagonRotation k)) ≠ 0) →
    cycleZCount A B v ≠ 1 ∧ cycleWCount A B v ≠ 1 ∧
    ¬(cycleZCount A B v = 4 ∧ cycleWCount A B v = 0 ∧ cycleDoubleCount A B v = 1) ∧
    ¬(cycleZCount A B v = 0 ∧ cycleWCount A B v = 4 ∧ cycleDoubleCount A B v = 1)

/-- Theorem 3.6 with its exact finite matrix counts. -/
theorem ScaledZWLimit.pentagon_matrix_rule {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) :
    PentagonMatrixRule l.z.matrix l.w.matrix := by
  classical
  intro v hv hedge
  have hne : ∀ k, v k ≠ v (pentagonRotation k) := by
    intro k h
    exact (by decide : ∀ k : Fin 5, k ≠ pentagonRotation k) k (hv h)
  have he : ∀ k, l.z.force (v k) (v (pentagonRotation k)) ≠ 0 ∨
      l.w.force (v k) (v (pentagonRotation k)) ≠ 0 :=
    fun k => (l.matrix_edge_iff _ _ (hne k)).mp (hedge k)
  have hz : cycleZCount l.z.matrix l.w.matrix v = (l.zOnlySides v pentagonRotation).card := by
    simp [cycleZCount, ScaledZWLimit.zOnlySides, OneColorLimit.matrix, OneColorLimit.Incident, hne]
  have hw : cycleWCount l.z.matrix l.w.matrix v = (l.wOnlySides v pentagonRotation).card := by
    simp [cycleWCount, ScaledZWLimit.wOnlySides, OneColorLimit.matrix, OneColorLimit.Incident, hne]
  have hd : cycleDoubleCount l.z.matrix l.w.matrix v = (l.doubleSides v pentagonRotation).card := by
    simp [cycleDoubleCount, ScaledZWLimit.doubleSides, OneColorLimit.matrix, OneColorLimit.Incident, hne]
  rw [hz, hw, hd]
  exact ⟨l.cycle_z_only_count_ne_one hb v pentagonRotation hne he,
    l.cycle_w_only_count_ne_one hb v pentagonRotation hne he,
    fun h => l.cycle_double_count_ne_one_of_no_w_only hb v pentagonRotation hne he h.2.1 h.2.2,
    fun h => l.cycle_double_count_ne_one_of_no_z_only hb v pentagonRotation hne he h.1 h.2.2⟩

end CentralConfigurations
