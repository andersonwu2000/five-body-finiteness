import CentralConfigurations.Diagrams.SecondaryTriangleMass

/-!
# Two closed triangle rows outside one small external cluster

The mechanism used in Sections 10.3 and 11.9--11.11. An external cluster
whose z-diameter is negligible relative to a pure z-triangle can approach
at most one triangle vertex on that scale. On a common refinement, the
other two rows discard every external w-force and give a kite mass branch.
-/

namespace CentralConfigurations

open Filter Asymptotics
open scoped Topology

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℝ}
  {q : ℕ → ZWSystem ℂ n (fun a => (mass a : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))

theorem w_stroke_z_separation_small_relative_pure_z
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j p r : Fin n) (hij : i ≠ j) (hpr : p ≠ r)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j = 0)
    (hp : l.w.force p r ≠ 0) :
    (fun t => (q t).z r - (q t).z p) =o[atTop]
      (fun t => (q t).z i - (q t).z j) := by
  let a := ZWSystem.pairEstimateData q hb i j hij
  let b := ZWSystem.pairEstimateData q hb p r hpr
  have hsmall := (a.single_z_separations ((l.pair_z_stroke_iff hb i j hij).mpr hz)
    ((l.pair_w_absent_iff hb i j hij).mpr hw)).1
  have hupper := b.swap.stroke_w_upper ((l.pair_w_stroke_iff hb p r hpr).mpr hp)
  exact (hupper.trans_isLittleO hsmall).neg_left.congr_left (fun t => by
    change -((q t).z p - (q t).z r) = _
    ring)

/-- This statement keeps all three possible pivot choices; no label choice
or asserted maximal-term table is an input. -/
theorem secondary_triangle_external_cluster_mass_cases
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (hm : ∀ a, 0 < mass a) (i j k p : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hp : p ∉ ({i, j, k} : Finset (Fin n)))
    (hpos : ∀ a ∈ ({i, j, k} : Finset (Fin n)), l.z.position a = 0)
    (hzij : l.z.force i j ≠ 0) (hzik : l.z.force i k ≠ 0)
    (hzjk : l.z.force j k ≠ 0)
    (hclosed : ∀ a ∈ ({i, j, k} : Finset (Fin n)),
      ∀ r ∉ ({i, j, k} : Finset (Fin n)), l.z.force a r = 0)
    (hcluster : ∀ r ∉ ({i, j, k} : Finset (Fin n)),
      (fun t => (q t).z r - (q t).z p) =o[atTop]
        (fun t => (q t).z i - (q t).z j)) :
    kiteMassPolynomial (mass i) (mass j) (mass k) = 0 ∨
    kiteMassPolynomial (mass j) (mass k) (mass i) = 0 ∨
    kiteMassPolynomial (mass k) (mass i) (mass j) = 0 := by
  classical
  let S : Finset (Fin n) := {i, j, k}
  obtain ⟨φ, hφ, htri⟩ := exists_simultaneous_order_trichotomy
    (fun a : Fin n => fun t => (q t).z a - (q t).z p)
    (fun _ : Fin n => fun t => (q t).z i - (q t).z j)
    (fun _ => Eventually.of_forall fun t => (q t).z_separation_ne_zero hij)
  let q' := fun t => q (φ t)
  let l' := l.comp φ hφ.tendsto_atTop
  have hb' : ∀ t, ‖(q' t).zVector‖ = ‖(q' t).wVector‖ := fun t => hb (φ t)
  let B := fun t => (q' t).z i - (q' t).z j
  let W := fun t => (q' t).wForce i j
  let Good (a : Fin n) := ∀ r ∉ S,
    (fun t => (q' t).wForce a r) =o[atTop] W
  have hi : i ∈ S := by simp [S]
  have hj : j ∈ S := by simp [S]
  have hk : k ∈ S := by simp [S]
  have hforce (a b : Fin n) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
      l'.z.force a b ≠ 0 := by
    have hji : l.z.force j i ≠ 0 := by rw [l.z.antisymm]; exact neg_ne_zero.mpr hzij
    have hki : l.z.force k i ≠ 0 := by rw [l.z.antisymm]; exact neg_ne_zero.mpr hzik
    have hkj : l.z.force k j ≠ 0 := by rw [l.z.antisymm]; exact neg_ne_zero.mpr hzjk
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first | exact (hab rfl).elim | assumption
  have hzorders := l'.z_triangle_orders hb' i j k hij hjk hik hzij hzjk hzik
  have hzbound (a b : Fin n) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
      B =Θ[atTop] (fun t => (q' t).z a - (q' t).z b) := by
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
    all_goals first
      | exact (hab rfl).elim
      | exact ⟨isBigO_refl _ _, isBigO_refl _ _⟩
      | exact hzorders.1
      | exact hzorders.2.1
      | simpa only [B, Asymptotics.IsTheta, isBigO_iff, norm_sub_rev] using hzorders.1
      | simpa only [B, Asymptotics.IsTheta, isBigO_iff, norm_sub_rev] using hzorders.2.1
      | simpa only [Asymptotics.IsTheta, isBigO_iff, norm_sub_rev, B] using
          (show B =Θ[atTop] B from ⟨isBigO_refl _ _, isBigO_refl _ _⟩)
  have hfar_good (a : Fin n) (ha : a ∈ S)
      (hf : B =O[atTop] (fun t => (q' t).z a - (q' t).z p)) : Good a := by
    intro r hr
    have har : a ≠ r := by intro he; exact hr (he ▸ ha)
    have hc : (fun t => (q' t).z r - (q' t).z p) =o[atTop] B :=
      (hcluster r hr).comp_tendsto hφ.tendsto_atTop
    have hc' := (hc.trans_isBigO hf).neg_right
    have hs : (fun t => (q' t).z r - (q' t).z p) =o[atTop]
        (fun t => (q' t).z p - (q' t).z a) :=
      hc'.congr_right (fun t => by ring)
    have ht := separation_theta_of_littleO hs
    have hza : B =O[atTop] (fun t => (q' t).z a - (q' t).z r) := by
      apply hf.trans
      simpa only [isBigO_iff, norm_sub_rev] using ht.1
    exact (ZWSystem.pairEstimateData q' hb' a r har).wForce_littleO_of_small_zForce
      (ZWSystem.pairEstimateData q' hb' i j hij)
      (l'.zForce_littleO_of_absent_stroke hb' a r i j har hij (hclosed a ha r hr) hzij) hza
  have hothers (a b : Fin n) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
      (hbad : ¬ Good a) : Good b := by
    have hs : (fun t => (q' t).z a - (q' t).z p) =o[atTop] B := by
      rcases htri a with h | h | h
      · exact h
      · exact (hbad (hfar_good a ha h.2)).elim
      · exact (hbad (hfar_good a ha h.isBigO)).elim
    have hs' : (fun t => (q' t).z p - (q' t).z a) =o[atTop]
        (fun t => (q' t).z a - (q' t).z b) :=
      (hs.trans_isBigO (hzbound a b ha hb hab).1).neg_left.congr_left (fun t => by ring)
    have ht := separation_theta_of_littleO hs'
    apply hfar_good b hb
    apply (hzbound a b ha hb hab).1.trans
    simpa only [isBigO_iff, norm_sub_rev] using ht.1
  have hrows (a b c : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (he : ({a, b, c} : Finset (Fin n)) = S) (hga : Good a) (hgb : Good b) :
      kiteMassPolynomial (mass a) (mass b) (mass c) = 0 := by
    have ha : a ∈ S := by rw [← he]; simp
    have hb : b ∈ S := by rw [← he]; simp
    have hc : c ∈ S := by rw [← he]; simp
    have hW := l'.wForce_theta_of_z_separation_strokes hb' a b i j hab hij
      (hforce a b ha hb hab) hzij (hzbound a b ha hb hab).symm
    apply l'.secondary_triangle_rows_mass_polynomial hb' hm a b c hab hac hbc
      (hpos a ha) (hpos b hb) (hforce a b ha hb hab)
      (hforce a c ha hc hac) (hforce b c hb hc hbc)
    · intro r hrb hrc
      by_cases hra : r = a
      · subst r; exact l'.z.diagonal a
      · exact hclosed a ha r (by change r ∉ S; rw [← he]; simpa using ⟨hra, hrb, hrc⟩)
    · intro r hra hrc
      by_cases hrb : r = b
      · subst r; exact l'.z.diagonal b
      · exact hclosed b hb r (by change r ∉ S; rw [← he]; simpa using ⟨hra, hrb, hrc⟩)
    · intro r hrb hrc
      by_cases hra : r = a
      · subst r
        simpa only [ZWSystem.wForce, sub_self, mul_zero] using
          (isLittleO_zero (fun t => (q' t).wForce a b) atTop)
      · exact (hga r (by rw [← he]; simpa using ⟨hra, hrb, hrc⟩)).trans_isBigO hW.2
    · intro r hra hrc
      by_cases hrb : r = b
      · subst r
        simpa only [ZWSystem.wForce, sub_self, mul_zero] using
          (isLittleO_zero (fun t => (q' t).wForce a b) atTop)
      · exact (hgb r (by rw [← he]; simpa using ⟨hra, hrb, hrc⟩)).trans_isBigO hW.2
  by_cases hgi : Good i
  · by_cases hgj : Good j
    · exact Or.inl (hrows i j k hij hik hjk rfl hgi hgj)
    · exact Or.inr (Or.inr (hrows k i j (Ne.symm hik) (Ne.symm hjk) hij
        (by ext a; simp [S]; tauto) (hothers j k hj hk hjk hgj) hgi))
  · exact Or.inr (Or.inl (hrows j k i hjk (Ne.symm hij) (Ne.symm hik)
      (by ext a; simp [S]; tauto) (hothers i j hi hj hij hgi) (hothers i k hi hk hik hgi)))

theorem secondary_triangle_external_w_star_mass_cases_of_code {d : DiagramCode n}
    (hd : l.diagramCode = d)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (hm : ∀ a, 0 < mass a) (i j k p : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hp : p ∉ ({i, j, k} : Finset (Fin n)))
    (hpos : ∀ a ∈ ({i, j, k} : Finset (Fin n)), d.1 (upperIndex a a) = false)
    (hz : d.1 (upperIndex i j) = true ∧ d.1 (upperIndex i k) = true ∧
      d.1 (upperIndex j k) = true)
    (hw : d.2 (upperIndex i j) = false)
    (hclosed : ∀ a ∈ ({i, j, k} : Finset (Fin n)),
      ∀ r ∉ ({i, j, k} : Finset (Fin n)), d.1 (upperIndex a r) = false)
    (hstar : ∀ r ∉ ({i, j, k} : Finset (Fin n)), r ≠ p → d.2 (upperIndex p r) = true) :
    kiteMassPolynomial (mass i) (mass j) (mass k) = 0 ∨
    kiteMassPolynomial (mass j) (mass k) (mass i) = 0 ∨
    kiteMassPolynomial (mass k) (mass i) (mass j) = 0 := by
  apply l.secondary_triangle_external_cluster_mass_cases hb hm i j k p hij hik hjk hp
    (fun a ha => l.z_position_zero_of_code hd a (hpos a ha))
    (l.z_force_ne_zero_of_code hd i j hij hz.1)
    (l.z_force_ne_zero_of_code hd i k hik hz.2.1)
    (l.z_force_ne_zero_of_code hd j k hjk hz.2.2)
    (fun a ha r hr => l.z_force_zero_of_code hd a r (hclosed a ha r hr))
  intro r hr
  by_cases he : r = p
  · subst r
    simpa only [sub_self] using (isLittleO_zero (fun t => (q t).z i - (q t).z j) atTop)
  · exact l.w_stroke_z_separation_small_relative_pure_z hb i j p r hij (Ne.symm he)
      (l.z_force_ne_zero_of_code hd i j hij hz.1) (l.w_force_zero_of_code hd i j hw)
      (l.w_force_ne_zero_of_code hd p r (Ne.symm he) (hstar r hr he))

end ScaledZWLimit
end CentralConfigurations
