import CentralConfigurations.FiveBody.Source18Geometry
import CentralConfigurations.Asymptotics.ClusterPairLimits

/-!
# The actual three-body limit of five-body source 18

Compactness is applied to the three small z-coordinates and all nine
inverse-distance entries on one subsequence. The two external bodies
are removed only after their rescaled force terms are proved to vanish.
The resulting object satisfies every equation of `ZWSystem`.
-/

namespace CentralConfigurations
open Filter Asymptotics
open scoped Topology BigOperators

theorem ZWSystem.five_body_first_three_z_div {mass : Fin 5 → ℂ}
    (q : ZWSystem ℂ 5 mass) (a : ℂ) (i : Fin 3) :
    q.z (i.castLE (by decide)) / a =
      (∑ j : Fin 3, mass (j.castLE (by decide)) *
        q.delta (i.castLE (by decide)) (j.castLE (by decide)) ^ 3 *
        (q.z (i.castLE (by decide)) / a - q.z (j.castLE (by decide)) / a)) +
      mass 3 * (q.zForce (i.castLE (by decide)) 3 / a) +
      mass 4 * (q.zForce (i.castLE (by decide)) 4 / a) := by
  have h := q.force_z (i.castLE (by decide))
  simp [Fin.sum_univ_succ] at h ⊢
  dsimp only [ZWSystem.zForce]
  linear_combination a⁻¹ * h

theorem ZWSystem.five_body_first_three_w_scaled {mass : Fin 5 → ℂ}
    (q : ZWSystem ℂ 5 mass) (a : ℂ) (i : Fin 3) :
    a * q.w (i.castLE (by decide)) =
      (∑ j : Fin 3, mass (j.castLE (by decide)) *
        q.delta (i.castLE (by decide)) (j.castLE (by decide)) ^ 3 *
        (a * q.w (i.castLE (by decide)) - a * q.w (j.castLE (by decide)))) +
      mass 3 * (a * q.wForce (i.castLE (by decide)) 3) +
      mass 4 * (a * q.wForce (i.castLE (by decide)) 4) := by
  have h := q.force_w (i.castLE (by decide))
  simp [Fin.sum_univ_succ] at h ⊢
  dsimp only [ZWSystem.wForce]
  linear_combination a * h

theorem ScaledZWLimit.five_body_source18_triangle_limit {mass : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun r => (mass r : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ r, 0 < mass r) (hd : l.diagramCode = fiveBodySourceDiagram 17)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    ∃ r : ZWSystem ℂ 3 (fun i => (mass (i.castLE (by decide)) : ℂ)),
      (∀ i, r.w i = l.w.position (i.castLE (by decide))) ∧
      (∀ i, r.w i ≠ 0) ∧ ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ i, Tendsto (fun t => (q (φ t)).z (i.castLE (by decide)) /
        (q (φ t)).inverseScale) atTop (𝓝 (r.z i))) ∧
      (∀ i j, Tendsto (fun t => (q (φ t)).delta (i.castLE (by decide))
        (j.castLE (by decide))) atTop (𝓝 (r.delta i j))) := by
  let e : Fin 3 → Fin 5 := fun i => i.castLE (by decide)
  have hs := inverseScale_ne_zero (q := q) 0 1 (by decide)
  have hwi : ∀ i : Fin 3, l.w.position (e i) ≠ 0 := by
    intro i
    apply l.w_position_ne_zero_of_code hd
    fin_cases i <;> decide +kernel
  have hzi : ∀ i : Fin 3, l.z.position (e i) = 0 := by
    intro i
    apply l.z_position_zero_of_code hd
    fin_cases i <;> decide +kernel
  have hWne := l.five_body_source18_triangle_injective hm hd
  have hsmall := (l.five_body_source18_small_positions hm hd).1
  let f : ℕ → (Fin 3 ⊕ (Fin 3 × Fin 3)) → ℂ := fun t c => match c with
    | .inl i => (q t).z (e i) / (q t).inverseScale
    | .inr (i,j) => (q t).delta (e i) (e j)
  have hbounded : ∀ c, Bornology.IsBounded (Set.range (fun t => f t c)) := by
    intro c
    rcases c with i | ⟨i,j⟩
    · exact bounded_range_div_of_bigO (hsmall i)
    · by_cases hij : i = j
      · subst j
        simpa only [f, ZWSystem.delta_diagonal] using
          (Metric.isBounded_range_of_tendsto (fun _ : ℕ => (0 : ℂ)) tendsto_const_nhds)
      · exact bounded_of_power_tendsto (by decide : (3 : ℕ) ≠ 0)
          (l.delta_cube_limit_of_w_positions_ne hs (e i) (e j)
            (fun h => hij (hWne h)))
  obtain ⟨v,φ,hφ,hlim⟩ := exists_finite_coordinate_limits f hbounded
  let Z : Fin 3 → ℂ := fun i => v (.inl i)
  let W : Fin 3 → ℂ := fun i => l.w.position (e i)
  let D : Fin 3 → Fin 3 → ℂ := fun i j => v (.inr (i,j))
  have hZ (i : Fin 3) : Tendsto
      (fun t => (q (φ t)).z (e i)/(q (φ t)).inverseScale) atTop (𝓝 (Z i)) :=
    hlim (.inl i)
  have hD (i j : Fin 3) : Tendsto
      (fun t => (q (φ t)).delta (e i) (e j)) atTop (𝓝 (D i j)) := hlim (.inr (i,j))
  have hW (i : Fin 3) : Tendsto
      (fun t => (q (φ t)).inverseScale * (q (φ t)).w (e i)) atTop (𝓝 (W i)) :=
    (l.w_position (e i)).comp hφ.tendsto_atTop
  have hcrossZ (i : Fin 3) (k : Fin 5) (hk : k = 3 ∨ k = 4) :
      Tendsto (fun t => (q (φ t)).zForce (e i) k / (q (φ t)).inverseScale)
        atTop (𝓝 0) := by
    have hzk : l.z.position k ≠ 0 := l.z_position_ne_zero_of_code hd k (by
      rcases hk with rfl | rfl <;> decide +kernel)
    have hwk : l.w.position k = 0 := l.w_position_zero_of_code hd k (by
      rcases hk with rfl | rfl <;> decide +kernel)
    exact (l.zForce_div_scale_zero_of_positions_ne hs ha (e i) k
      (by rw [hzi i]; exact hzk.symm) (by rw [hwk]; exact hwi i)).comp hφ.tendsto_atTop
  have hcrossW (i : Fin 3) (k : Fin 5) (hk : k = 3 ∨ k = 4) :
      Tendsto (fun t => (q (φ t)).inverseScale * (q (φ t)).wForce (e i) k)
        atTop (𝓝 0) := by
    have hf := l.w_force_zero_of_code hd (e i) k (by
      rcases hk with rfl | rfl <;> fin_cases i <;> decide +kernel)
    simpa only [hf] using (l.w_force (e i) k).comp hφ.tendsto_atTop
  have hsymm : ∀ i j, D i j = D j i := by
    intro i j
    exact tendsto_nhds_unique (hD i j)
      ((hD j i).congr' (Eventually.of_forall fun t => (q (φ t)).delta_symm (e j) (e i)))
  have hdiag : ∀ i, D i i = 0 := by
    intro i
    have h := hD i i
    simp only [ZWSystem.delta_diagonal] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hforceZ : ∀ i, Z i = ∑ j, (mass (e j) : ℂ) * D i j ^ 3 * (Z i-Z j) := by
    intro i
    have hS := tendsto_finsetSum Finset.univ (fun j _ =>
      (((hD i j).pow 3).const_mul (mass (e j) : ℂ)).mul ((hZ i).sub (hZ j)))
    have hR := (hS.add ((hcrossZ i 3 (Or.inl rfl)).const_mul (mass 3 : ℂ))).add
      ((hcrossZ i 4 (Or.inr rfl)).const_mul (mass 4 : ℂ))
    simp only [mul_zero, add_zero] at hR
    have he (t : ℕ) := (q (φ t)).five_body_first_three_z_div (q (φ t)).inverseScale i
    exact tendsto_nhds_unique (hZ i) (hR.congr' (Eventually.of_forall fun t => (he t).symm))
  have hforceW : ∀ i, W i = ∑ j, (mass (e j) : ℂ) * D i j ^ 3 * (W i-W j) := by
    intro i
    have hS := tendsto_finsetSum Finset.univ (fun j _ =>
      (((hD i j).pow 3).const_mul (mass (e j) : ℂ)).mul ((hW i).sub (hW j)))
    have hR := (hS.add ((hcrossW i 3 (Or.inl rfl)).const_mul (mass 3 : ℂ))).add
      ((hcrossW i 4 (Or.inr rfl)).const_mul (mass 4 : ℂ))
    simp only [mul_zero, add_zero] at hR
    have he (t : ℕ) := (q (φ t)).five_body_first_three_w_scaled (q (φ t)).inverseScale i
    exact tendsto_nhds_unique (hW i) (hR.congr' (Eventually.of_forall fun t => (he t).symm))
  have hdist : ∀ i j, i ≠ j → D i j ^ 2 * ((Z i-Z j)*(W i-W j)) = 1 := by
    intro i j hij
    have heij : e i ≠ e j := by
      intro he
      apply hij
      exact Fin.ext (congrArg (fun k : Fin 5 => k.val) he)
    have h := ((hD i j).pow 2).mul (((hZ i).sub (hZ j)).mul ((hW i).sub (hW j)))
    have he (t : ℕ) : (q (φ t)).delta (e i) (e j)^2 *
        (((q (φ t)).z (e i)/(q (φ t)).inverseScale -
          (q (φ t)).z (e j)/(q (φ t)).inverseScale) *
        ((q (φ t)).inverseScale*(q (φ t)).w (e i) -
          (q (φ t)).inverseScale*(q (φ t)).w (e j))) = 1 := by
      convert (q (φ t)).distance (e i) (e j) heij using 1
      field_simp [hs (φ t)]
    simp only [he] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  let r : ZWSystem ℂ 3 (fun i => (mass (i.castLE (by decide)) : ℂ)) :=
    ⟨Z,W,D,hsymm,hdiag,hforceZ,hforceW,hdist⟩
  exact ⟨r,fun _ => rfl,hwi,φ,hφ,hZ,hD⟩

end CentralConfigurations
