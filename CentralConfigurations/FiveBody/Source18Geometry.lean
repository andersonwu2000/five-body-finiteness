import CentralConfigurations.FiveBody.Source19Geometry

/-!
# The fully circled triangle in five-body source 18

This is the pair/triangle diagram treated separately in Albouy--Kaloshin,
Section 8.2, and cited in Chang, Section 10.8. The triangle has three
distinct leading positions. Their opposite coordinates are on the small
scale. All statements concern an actual solution sequence.
-/

namespace CentralConfigurations
open Filter Asymptotics
open scoped Topology

namespace ScaledZWLimit

/-- In a three-vertex component, coincidence of two circled positions
would isolate the third. Its row equation and its two strokes contradict
that coincidence. The other leading positions are zero. -/
theorem w_positions_ne_in_circled_triangle
    {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun r => (mass r : ℂ))} {a : ℕ → ℂ}
    (l : ScaledZWLimit q a) (hs : ∀ t, a t ≠ 0)
    (i j k : Fin n) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    (hmi : 0 < mass i) (hmj : 0 < mass j) (hmk : 0 < mass k)
    (hi : l.w.position i ≠ 0) (hk : l.w.position k ≠ 0)
    (hb : (mass i : ℂ) * l.w.position i + mass j * l.w.position j +
      mass k * l.w.position k = 0)
    (hout : ∀ r, r ≠ i → r ≠ j → r ≠ k → l.w.position r = 0)
    (hfi : l.w.force k i ≠ 0) (hfj : l.w.force k j ≠ 0) :
    l.w.position i ≠ l.w.position j := by
  intro he
  have hsum : (mass i : ℂ) + mass j + mass k ≠ 0 := by
    exact_mod_cast ne_of_gt (add_pos (add_pos hmi hmj) hmk)
  have hkiP : l.w.position k ≠ l.w.position i := by
    intro heki
    apply mul_ne_zero hsum hi
    rw [← he, heki] at hb
    linear_combination hb
  have hkjP : l.w.position k ≠ l.w.position j := by rwa [← he]
  have hzk := l.z_position_bigO_scale_of_isolated_w_position hs k (by
    intro r hr
    by_cases hri : r = i
    · simpa only [hri] using hkiP
    by_cases hrj : r = j
    · simpa only [hrj] using hkjP
    exact fun h => hk (h.trans (hout r hri hrj hr)))
  have hzi := (hzk.sub (l.z_separation_bigO_scale_of_maximal_w_pair
    hs k i hki hfi hkiP)).congr_left (fun t =>
      show (q t).z k - ((q t).z k - (q t).z i) = (q t).z i by ring)
  have hzj := (hzk.sub (l.z_separation_bigO_scale_of_maximal_w_pair
    hs k j hkj hfj hkjP)).congr_left (fun t =>
      show (q t).z k - ((q t).z k - (q t).z j) = (q t).z j by ring)
  exact l.w_positions_ne_of_z_separation_bigO_scale hs i j hij (hzi.sub hzj) he

variable {mass : Fin 5 → ℝ}
  {q : ℕ → ZWSystem ℂ 5 (fun r => (mass r : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ r, 0 < mass r) (hd : l.diagramCode = fiveBodySourceDiagram 17)
include hm hd

theorem five_body_source18_triangle_distinct :
    l.w.position 0 ≠ l.w.position 1 ∧
    l.w.position 0 ≠ l.w.position 2 ∧
    l.w.position 1 ≠ l.w.position 2 := by
  have hs := inverseScale_ne_zero (q := q) 0 1 (by decide)
  have h0 := l.w_position_ne_zero_of_code hd 0 (by decide +kernel)
  have h1 := l.w_position_ne_zero_of_code hd 1 (by decide +kernel)
  have h2 := l.w_position_ne_zero_of_code hd 2 (by decide +kernel)
  have h3 := l.w_position_zero_of_code hd 3 (by decide +kernel)
  have h4 := l.w_position_zero_of_code hd 4 (by decide +kernel)
  have hb : (mass 0 : ℂ) * l.w.position 0 + mass 1 * l.w.position 1 +
      mass 2 * l.w.position 2 = 0 := by
    simpa [add_assoc] using l.w_component_balance_of_code hd {0,1,2} (by decide +kernel)
  refine ⟨?_, ?_, ?_⟩
  · apply l.w_positions_ne_in_circled_triangle hs 0 1 2 (by decide) (by decide)
      (by decide) (hm 0) (hm 1) (hm 2) h0 h2 hb
    · intro r hr0 hr1 hr2
      fin_cases r <;> simp_all
    · exact l.w_force_ne_zero_of_code hd 2 0 (by decide) (by decide +kernel)
    · exact l.w_force_ne_zero_of_code hd 2 1 (by decide) (by decide +kernel)
  · apply l.w_positions_ne_in_circled_triangle hs 0 2 1 (by decide) (by decide)
      (by decide) (hm 0) (hm 2) (hm 1) h0 h1 (by linear_combination hb)
    · intro r hr0 hr2 hr1
      fin_cases r <;> simp_all
    · exact l.w_force_ne_zero_of_code hd 1 0 (by decide) (by decide +kernel)
    · exact l.w_force_ne_zero_of_code hd 1 2 (by decide) (by decide +kernel)
  · apply l.w_positions_ne_in_circled_triangle hs 1 2 0 (by decide) (by decide)
      (by decide) (hm 1) (hm 2) (hm 0) h1 h0 (by linear_combination hb)
    · intro r hr1 hr2 hr0
      fin_cases r <;> simp_all
    · exact l.w_force_ne_zero_of_code hd 0 1 (by decide) (by decide +kernel)
    · exact l.w_force_ne_zero_of_code hd 0 2 (by decide) (by decide +kernel)

theorem five_body_source18_triangle_injective :
    Function.Injective (fun i : Fin 3 => l.w.position (i.castLE (by decide))) := by
  obtain ⟨h01,h02,h12⟩ := l.five_body_source18_triangle_distinct hm hd
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [Fin.castLE]

theorem five_body_source18_small_positions :
    (∀ i : Fin 3, (fun t => (q t).z (i.castLE (by decide))) =O[atTop]
      (fun t => (q t).inverseScale)) ∧
    (fun t => (q t).w 3) =O[atTop] (fun t => (q t).inverseScale) ∧
    (fun t => (q t).w 4) =O[atTop] (fun t => (q t).inverseScale) := by
  obtain ⟨h01,h02,h12⟩ := l.five_body_source18_triangle_distinct hm hd
  have hs := inverseScale_ne_zero (q := q) 0 1 (by decide)
  have hz0 := l.z_position_zero_of_code hd 0 (by decide +kernel)
  have hz1 := l.z_position_zero_of_code hd 1 (by decide +kernel)
  have hz2 := l.z_position_zero_of_code hd 2 (by decide +kernel)
  have hz3 := l.z_position_ne_zero_of_code hd 3 (by decide +kernel)
  have hz4 := l.z_position_ne_zero_of_code hd 4 (by decide +kernel)
  have hw0 := l.w_position_ne_zero_of_code hd 0 (by decide +kernel)
  have hw1 := l.w_position_ne_zero_of_code hd 1 (by decide +kernel)
  have hw2 := l.w_position_ne_zero_of_code hd 2 (by decide +kernel)
  have hw3 := l.w_position_zero_of_code hd 3 (by decide +kernel)
  have hw4 := l.w_position_zero_of_code hd 4 (by decide +kernel)
  have hb : (mass 3 : ℂ) * l.z.position 3 + mass 4 * l.z.position 4 = 0 := by
    simpa using l.z_component_balance_of_code hd {3,4} (by decide +kernel)
  have h34 := positive_pair_balance_distinct _ _ (hm 3) (hm 4) _ _ hz3 hb
  refine ⟨?_, ?_, ?_⟩
  · intro i
    apply l.z_position_bigO_scale_of_isolated_w_position hs
    intro j hj
    fin_cases i <;> fin_cases j <;> simp_all [Fin.castLE] <;> aesop
  · apply l.swapAtScale.z_position_bigO_scale_of_isolated_w_position hs 3
    intro j hj
    change l.z.position 3 ≠ l.z.position j
    fin_cases j <;> simp_all
  · apply l.swapAtScale.z_position_bigO_scale_of_isolated_w_position hs 4
    intro j hj
    change l.z.position 4 ≠ l.z.position j
    fin_cases j <;> simp_all
    exact fun h => h34 h.symm

end ScaledZWLimit
end CentralConfigurations
