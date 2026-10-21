import CentralConfigurations.FiveBody.D2HZero.CubePair

namespace CentralConfigurations.FiveBody.D2.HZero
set_option maxHeartbeats 3000000

theorem exists_ordered_pair {i j : Fin 3} (hij : i ≠ j) :
    ∃ e : Fin 3 ≃ Fin 3, e 0=i ∧ e 1=j := by
  fin_cases i <;> fin_cases j <;> try exact (hij rfl).elim
  all_goals first
    | exact ⟨Equiv.refl _,by decide +kernel,by decide +kernel⟩
    | exact ⟨Equiv.swap (0 : Fin 3) 1,by decide +kernel,by decide +kernel⟩
    | exact ⟨Equiv.swap (0 : Fin 3) 2,by decide +kernel,by decide +kernel⟩
    | exact ⟨Equiv.swap (1 : Fin 3) 2,by decide +kernel,by decide +kernel⟩
    | exact ⟨(Equiv.swap (0 : Fin 3) 1).trans (Equiv.swap 1 2),by decide +kernel,by decide +kernel⟩
    | exact ⟨(Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap 0 1),by decide +kernel,by decide +kernel⟩

/-- A single common permutation and scale of the original triangle, not a new root sheet. -/
structure CircleChart {m : Fin 5 → ℝ} (s : FiveBodySource18Certificate m) where
  order : Fin 3 ≃ Fin 3
  h : ℂ
  h_square : h^2+3=0
  pair_ratio : s.triangle.w (order 1)/s.triangle.w (order 0)=(h-1)/2
  third_norm : ‖s.triangle.w (order 2)/s.triangle.w (order 0)‖=1

noncomputable def CircleChart.gamma {m : Fin 5 → ℝ}
    {s : FiveBodySource18Certificate m} (c : CircleChart s) : ℂ := s.triangle.w (c.order 0)

noncomputable def CircleChart.omega {m : Fin 5 → ℝ}
    {s : FiveBodySource18Certificate m} (c : CircleChart s) : ℂ := (c.h-1)/2

noncomputable def CircleChart.y {m : Fin 5 → ℝ}
    {s : FiveBodySource18Certificate m} (c : CircleChart s) : ℂ := s.triangle.w (c.order 2)/c.gamma

theorem CircleChart.gamma_ne_zero {m : Fin 5 → ℝ}
    {s : FiveBodySource18Certificate m} (c : CircleChart s) : c.gamma ≠ 0 := s.w_ne_zero _

theorem CircleChart.omega_ne_one {m : Fin 5 → ℝ}
    {s : FiveBodySource18Certificate m} (c : CircleChart s) : c.omega ≠ 1 := by
  intro h
  have he := (div_eq_iff c.gamma_ne_zero).mp (c.pair_ratio.trans h)
  have hd := s.triangle.w_separation_ne_zero (c.order.injective.ne (by decide : (1 : Fin 3) ≠ 0))
  apply hd
  dsimp [CircleChart.gamma] at he
  simpa using sub_eq_zero.mpr (by simpa using he)

theorem CircleChart.y_ne_one {m : Fin 5 → ℝ}
    {s : FiveBodySource18Certificate m} (c : CircleChart s) : c.y ≠ 1 := by
  intro h
  have he := (div_eq_iff c.gamma_ne_zero).mp h
  have hd := s.triangle.w_separation_ne_zero (c.order.injective.ne (by decide : (2 : Fin 3) ≠ 0))
  apply hd
  dsimp [CircleChart.gamma] at he
  simpa using sub_eq_zero.mpr (by simpa using he)

theorem CircleChart.y_ne_omega {m : Fin 5 → ℝ}
    {s : FiveBodySource18Certificate m} (c : CircleChart s) : c.y ≠ c.omega := by
  intro h
  have he : s.triangle.w (c.order 2)/c.gamma=s.triangle.w (c.order 1)/c.gamma :=
    h.trans c.pair_ratio.symm
  have hpos := (div_left_inj' c.gamma_ne_zero).mp he
  exact s.triangle.w_separation_ne_zero (c.order.injective.ne (by decide : (2 : Fin 3) ≠ 1))
    (sub_eq_zero.mpr hpos)

theorem exists_circleChart {m : Fin 5 → ℝ} (s : FiveBodySource18Certificate m)
    (hm : ∀ i, 0 < m i) (hzero : ∀ i, centeredCrossResponse s i=0) :
    Nonempty (CircleChart s) := by
  obtain ⟨K,hK⟩ := exists_cross_multiple_of_zero s hzero
  have hn := equal_norms_of_cross_multiple s hm hK
  obtain ⟨i,j,hij,hcube⟩ := exists_cube_equal_pair_of_cross_multiple s hm hK
  have hneq : s.triangle.w j ≠ s.triangle.w i := by
    intro he
    exact s.triangle.w_separation_ne_zero hij (by rw [he,sub_self])
  obtain ⟨h,hh,hpair,_⟩ := primitive_ratio (s.w_ne_zero i) hneq hcube
  obtain ⟨e,he0,he1⟩ := exists_ordered_pair hij
  refine ⟨⟨e,h,hh,?_,?_⟩⟩
  · simpa [he0,he1] using hpair
  · rw [norm_div,hn (e 2) (e 0)]
    exact div_self (norm_ne_zero_iff.mpr (s.w_ne_zero _))

end CentralConfigurations.FiveBody.D2.HZero
