import CentralConfigurations.Asymptotics.OrderSemantics
import Mathlib.Topology.Order.Compact

/-!
# Simultaneous order comparisons after subsequence extraction

Section 4 does not assume that every variable has a power-law order. A finite
family can nevertheless be compared with finitely many scale functions after
one common subsequence extraction. The bounded ratio below includes zero
variables and has three possible limit regimes: smaller, comparable, larger.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

noncomputable def orderBalance (f g : ℕ → ℂ) (t : ℕ) : ℝ :=
  ‖f t‖ / (‖f t‖ + ‖g t‖)

theorem orderBalance_mem_Icc (f g : ℕ → ℂ) (t : ℕ) :
    orderBalance f g t ∈ Set.Icc (0 : ℝ) 1 := by
  have hf := norm_nonneg (f t)
  have hg := norm_nonneg (g t)
  refine ⟨div_nonneg hf (add_nonneg hf hg), ?_⟩
  by_cases h : ‖f t‖ + ‖g t‖ = 0
  · simp [orderBalance, h]
  · have hp : 0 < ‖f t‖ + ‖g t‖ := lt_of_le_of_ne (add_nonneg hf hg) (Ne.symm h)
    exact (div_le_one hp).mpr (by linarith)

theorem norm_div_eq_orderBalance {f g : ℕ → ℂ}
    (hg : ∀ᶠ t in atTop, g t ≠ 0) :
    (fun t => ‖f t‖ / ‖g t‖) =ᶠ[atTop]
      (fun t => orderBalance f g t / (1 - orderBalance f g t)) := by
  filter_upwards [hg] with t ht
  have hn : ‖g t‖ ≠ 0 := norm_ne_zero_iff.mpr ht
  have hp : 0 < ‖f t‖ + ‖g t‖ := add_pos_of_nonneg_of_pos (norm_nonneg _) (norm_pos_iff.mpr ht)
  unfold orderBalance
  have hd : 1 - ‖f t‖ / (‖f t‖ + ‖g t‖) ≠ 0 := by
    have hlt : ‖f t‖ / (‖f t‖ + ‖g t‖) < 1 :=
      (div_lt_one hp).mpr (by simpa using norm_pos_iff.mpr ht)
    linarith
  field_simp [hn, ne_of_gt hp, hd]
  <;> ring

theorem littleO_of_orderBalance_zero {f g : ℕ → ℂ}
    (hg : ∀ᶠ t in atTop, g t ≠ 0)
    (h : Tendsto (orderBalance f g) atTop (𝓝 0)) : f =o[atTop] g := by
  apply IsLittleO.of_norm_norm
  apply (isLittleO_iff_tendsto' (hg.mono (fun t ht hzero =>
    (ht (norm_eq_zero.mp hzero)).elim))).mpr
  have hh : Tendsto (fun t => orderBalance f g t / (1 - orderBalance f g t))
      atTop (𝓝 0) := by
    simpa using h.div (tendsto_const_nhds.sub h) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  exact hh.congr' (norm_div_eq_orderBalance hg).symm

theorem orderBalance_swap {f g : ℕ → ℂ}
    (hg : ∀ᶠ t in atTop, g t ≠ 0) :
    orderBalance g f =ᶠ[atTop] (fun t => 1 - orderBalance f g t) := by
  filter_upwards [hg] with t ht
  have hp : 0 < ‖f t‖ + ‖g t‖ := add_pos_of_nonneg_of_pos (norm_nonneg _) (norm_pos_iff.mpr ht)
  unfold orderBalance
  rw [add_comm ‖g t‖ ‖f t‖]
  field_simp
  ring

theorem littleO_of_orderBalance_one {f g : ℕ → ℂ}
    (hg : ∀ᶠ t in atTop, g t ≠ 0)
    (h : Tendsto (orderBalance f g) atTop (𝓝 1)) : g =o[atTop] f := by
  have hf : ∀ᶠ t in atTop, f t ≠ 0 := by
    filter_upwards [h.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with t ht
    intro hzero
    exact ht (by simp [orderBalance, hzero])
  apply littleO_of_orderBalance_zero hf
  have hh : Tendsto (fun t => 1 - orderBalance f g t) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub h
  exact hh.congr' (orderBalance_swap hg).symm

theorem theta_of_orderBalance_interior {f g : ℕ → ℂ} {v : ℝ}
    (hg : ∀ᶠ t in atTop, g t ≠ 0)
    (h : Tendsto (orderBalance f g) atTop (𝓝 v)) (hv : 0 < v) (hv1 : v < 1) :
    f =Θ[atTop] g := by
  have h1 : 1 - v ≠ 0 := ne_of_gt (sub_pos.mpr hv1)
  have hdiv : Tendsto (fun t => ‖f t‖ / ‖g t‖) atTop (𝓝 (v / (1 - v))) :=
    (h.div (tendsto_const_nhds.sub h) h1).congr' (norm_div_eq_orderBalance hg).symm
  have ht := (isTheta_of_div_tendsto_nhds_ne_zero hdiv (div_ne_zero (ne_of_gt hv) h1)).symm
  exact ht.of_norm_left.of_norm_right

/-- One subsequence simultaneously compares every supplied variable/scale pair.
The finite index type may itself be a product of variable and threshold indices. -/
theorem exists_simultaneous_order_trichotomy {ι : Type*} [Fintype ι]
    (f g : ι → ℕ → ℂ) (hg : ∀ i, ∀ᶠ t in atTop, g i t ≠ 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i,
      (f i ∘ φ) =o[atTop] (g i ∘ φ) ∨
      (f i ∘ φ) =Θ[atTop] (g i ∘ φ) ∨
      (g i ∘ φ) =o[atTop] (f i ∘ φ) := by
  let v : ℕ → ι → ℝ := fun t i => orderBalance (f i) (g i) t
  obtain ⟨a, ha, φ, hφ, hlim⟩ :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : ι → ℝ) 1)).tendsto_subseq
      (fun t => show v t ∈ Set.Icc (0 : ι → ℝ) 1 from
        ⟨fun i => (orderBalance_mem_Icc (f i) (g i) t).1,
         fun i => (orderBalance_mem_Icc (f i) (g i) t).2⟩)
  refine ⟨φ, hφ, fun i => ?_⟩
  have hi : Tendsto (orderBalance (f i ∘ φ) (g i ∘ φ)) atTop (𝓝 (a i)) :=
    ((continuous_apply i).tendsto a).comp hlim
  have hgi : ∀ᶠ t in atTop, (g i ∘ φ) t ≠ 0 := hφ.tendsto_atTop.eventually (hg i)
  by_cases hz : a i = 0
  · exact Or.inl (littleO_of_orderBalance_zero hgi (hz ▸ hi))
  by_cases ho : a i = 1
  · exact Or.inr (Or.inr (littleO_of_orderBalance_one hgi (ho ▸ hi)))
  · exact Or.inr (Or.inl (theta_of_orderBalance_interior hgi hi
      (lt_of_le_of_ne (ha.1 i) (Ne.symm hz)) (lt_of_le_of_ne (ha.2 i) ho)))

end CentralConfigurations
