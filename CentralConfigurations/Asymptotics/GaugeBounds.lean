import CentralConfigurations.Asymptotics.Balancing

/-!
# Gauge prevents either vector norm from vanishing

Section 2.2 of Chang (2023). We prove a uniform lower bound of 1/2, sufficient
for the argument (no sharp constant is asserted). The sign of the complex
inverse-distance branch is irrelevant: the proof uses a squared identity.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

theorem ZWSystem.norm_z_le {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i : Fin n) : ‖q.z i‖ ≤ ‖q.zVector‖ :=
  norm_le_pi_norm q.zVector (.inl i)

theorem ZWSystem.norm_zForce_le {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) : ‖q.zForce i j‖ ≤ ‖q.zVector‖ :=
  norm_le_pi_norm q.zVector (.inr (i, j))

theorem ZWSystem.norm_z_separation_le {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) : ‖q.z i - q.z j‖ ≤ 2 * ‖q.zVector‖ := by
  calc
    _ ≤ ‖q.z i‖ + ‖q.z j‖ := norm_sub_le _ _
    _ ≤ ‖q.zVector‖ + ‖q.zVector‖ := add_le_add (q.norm_z_le i) (q.norm_z_le j)
    _ = _ := by ring

theorem ZWSystem.gauge_force_identity {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j)
    (hg : q.z i - q.z j = q.w i - q.w j) :
    q.zForce i j ^ 2 * (q.z i - q.z j) ^ 4 = 1 := by
  have hd := q.distance i j hij
  rw [← hg] at hd
  calc
    _ = (q.delta i j ^ 2 * ((q.z i - q.z j) * (q.z i - q.z j))) ^ 3 := by
      unfold zForce
      ring
    _ = _ := by rw [hd]; norm_num

theorem ZWSystem.gauge_z_norm_lower_bound {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j)
    (hg : q.z i - q.z j = q.w i - q.w j) : (1 / 2 : ℝ) ≤ ‖q.zVector‖ := by
  have heq := congrArg norm (q.gauge_force_identity i j hij hg)
  simp only [norm_mul, norm_pow, norm_one] at heq
  by_contra hnot
  have hsmall : ‖q.zVector‖ < (1 / 2 : ℝ) := lt_of_not_ge hnot
  have hf : ‖q.zForce i j‖ < 1 :=
    (q.norm_zForce_le i j).trans_lt (hsmall.trans (by norm_num))
  have hd : ‖q.z i - q.z j‖ < 1 := by
    have hb := q.norm_z_separation_le i j
    linarith
  have hprod : ‖q.zForce i j‖ ^ 2 * ‖q.z i - q.z j‖ ^ 4 < 1 :=
    (mul_le_of_le_one_right (sq_nonneg _) (pow_le_one₀ (norm_nonneg _) hd.le)).trans_lt
      (pow_lt_one₀ (norm_nonneg _) hf (by decide : (2 : ℕ) ≠ 0))
  rw [heq] at hprod
  exact lt_irrefl _ hprod

theorem ZWSystem.gauge_w_norm_lower_bound {n : ℕ} {mass : Fin n → ℂ}
    (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j)
    (hg : q.z i - q.z j = q.w i - q.w j) : (1 / 2 : ℝ) ≤ ‖q.wVector‖ :=
  q.swap.gauge_z_norm_lower_bound i j hij hg.symm

theorem gauge_norm_product_tendsto {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j)
    (hg : ∀ t, (q t).z i - (q t).z j = (q t).w i - (q t).w j)
    (hmax : Tendsto (fun t => max ‖(q t).zVector‖ ‖(q t).wVector‖) atTop atTop) :
    Tendsto (fun t => ‖(q t).zVector‖ * ‖(q t).wVector‖) atTop atTop := by
  have hbound (t : ℕ) : (1 / 2 : ℝ) * max ‖(q t).zVector‖ ‖(q t).wVector‖ ≤
      ‖(q t).zVector‖ * ‖(q t).wVector‖ := by
    have hz := (q t).gauge_z_norm_lower_bound i j hij (hg t)
    have hw := (q t).gauge_w_norm_lower_bound i j hij (hg t)
    rcases le_total ‖(q t).zVector‖ ‖(q t).wVector‖ with hle | hle
    · rw [max_eq_right hle]
      nlinarith [mul_nonneg (sub_nonneg.mpr hz) (norm_nonneg (q t).wVector)]
    · rw [max_eq_left hle]
      nlinarith [mul_nonneg (sub_nonneg.mpr hw) (norm_nonneg (q t).zVector)]
  exact tendsto_atTop_mono hbound
    ((tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).mpr hmax)

theorem NormalizedSystem.toZW_gauge {n : ℕ} {mass : Fin n → ℂ}
    (q : NormalizedSystem ℂ n mass) (i j : Fin n) (hg : q.InGauge i j) :
    q.toZW.z i - q.toZW.z j = q.toZW.w i - q.toZW.w j :=
  (zw_gauge_iff (q.x i) (q.y i) (q.x j) (q.y j)).mpr hg.2

/-- From normalized, gauged solutions with norms tending to infinity to an
actual nonzero two-color limit in the balanced normalization. -/
theorem exists_gauged_singular_limit {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → NormalizedSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j)
    (hg : ∀ t, (q t).InGauge i j)
    (hmax : Tendsto (fun t => max ‖(q t).toZW.zVector‖ ‖(q t).toZW.wVector‖) atTop atTop) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale) atTop (𝓝 0) := by
  apply exists_balanced_singular_limit
  exact gauge_norm_product_tendsto (fun t => (q t).toZW) i j hij
    (fun t => (q t).toZW_gauge i j (hg t)) hmax

end CentralConfigurations
