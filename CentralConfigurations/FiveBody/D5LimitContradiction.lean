import CentralConfigurations.FiveBody.D5PositionLimits

namespace CentralConfigurations.FiveBody.D5
open Filter Asymptotics
open scoped Topology BigOperators

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  {s r : ℕ → ℂ}

theorem PositionLimit.false_of_collapsed_triple (L : PositionLimit q s r)
    (hm : ∀ i, 0 < m i)
    (hs : ∀ t, s t ≠ 0) (hr : ∀ t, r t ≠ 0)
    (hprod : Tendsto (fun t => (s t*r t)⁻¹) atTop (𝓝 0))
    {I : ℂ} (hI : ∀ t, (q t).toNormalized.potential=I)
    (hz : ∀ i : Fin 5, i<3 → L.z i=L.z 0)
    (hw : ∀ i : Fin 5, i<3 → L.w i=L.w 0)
    (hzn : ‖L.z‖=1) (hwn : ‖L.w‖=1) : False := by
  have hm0 := hm 0; have hm1 := hm 1; have hm2 := hm 2
  have hm3 := hm 3; have hm4 := hm 4
  let K : ℂ := m 0+m 1+m 2
  have hK : K ≠ 0 := by
    change ((m 0 : ℂ)+(m 1 : ℂ)+(m 2 : ℂ)) ≠ 0
    exact_mod_cast ne_of_gt (show 0 < m 0+m 1+m 2 by positivity)
  have h3 : (m 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm 3))
  have h4 : (m 4 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm 4))
  have hK3 : K+(m 3 : ℂ) ≠ 0 := by
    dsimp [K]
    exact_mod_cast ne_of_gt (show 0 < m 0+m 1+m 2+m 3 by positivity)
  have hK4 : K+(m 4 : ℂ) ≠ 0 := by
    dsimp [K]
    exact_mod_cast ne_of_gt (show 0 < m 0+m 1+m 2+m 4 by positivity)
  have h34 : (m 3 : ℂ)+(m 4 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (add_pos (hm 3) (hm 4))
  have hM : K+(m 3 : ℂ)+(m 4 : ℂ) ≠ 0 := by
    dsimp [K]
    exact_mod_cast ne_of_gt (show 0 < m 0+m 1+m 2+m 3+m 4 by positivity)
  have hz1 := hz 1 (by decide); have hz2 := hz 2 (by decide)
  have hw1 := hw 1 (by decide); have hw2 := hw 2 (by decide)
  have hcz : K*L.z 0+(m 3:ℂ)*L.z 3+(m 4:ℂ)*L.z 4=0 := by
    have h := L.center_z
    simp [Fin.sum_univ_succ,hz1,hz2] at h
    dsimp [K]; linear_combination h
  have hcw : K*L.w 0+(m 3:ℂ)*L.w 3+(m 4:ℂ)*L.w 4=0 := by
    have h := L.center_w
    simp [Fin.sum_univ_succ,hw1,hw2] at h
    dsimp [K]; linear_combination h
  have hci : K*L.z 0*L.w 0+(m 3:ℂ)*L.z 3*L.w 3+(m 4:ℂ)*L.z 4*L.w 4=0 := by
    have h := L.inertia_zero hI hprod
    simp [Fin.sum_univ_succ,hz1,hz2,hw1,hw2] at h
    dsimp [K]; linear_combination h
  have hnz : ¬ (L.z 0=0 ∧ L.z 3=0 ∧ L.z 4=0) := by
    intro hh
    have hh0 : L.z=0 := by funext i; fin_cases i <;> simp_all
    simp [hh0] at hzn
  have hnw : ¬ (L.w 0=0 ∧ L.w 3=0 ∧ L.w 4=0) := by
    intro hh
    have hh0 : L.w=0 := by funext i; fin_cases i <;> simp_all
    simp [hh0] at hwn
  apply three_block_null_impossible hK h3 h4 hK3 hK4 h34 hM hcz hcw hci hnz hnw
  · intro h03 h04
    let A : Finset (Fin 5) := {0,1,2}
    have hA : ∀ i∈A, ∀ j∈Aᶜ, (L.z i-L.z j)*(L.w i-L.w j) ≠ 0 := by
      intro i hi j hj
      have hi' : i<3 := by simp only [A,Finset.mem_insert,Finset.mem_singleton] at hi; rcases hi with rfl | rfl | rfl <;> decide
      have hj' : j=3 ∨ j=4 := by fin_cases j <;> simp_all [A]
      rw [hz i hi',hw i hi']
      rcases hj' with rfl | rfl
      · exact h03
      · exact h04
    have hhZ := L.isolated_block_z hs hr hprod A hA
    have hhW := L.isolated_block_w hs hr hprod A hA
    have hhZ' : K*L.z 0=0 := by
      simp [A,hz1,hz2] at hhZ
      dsimp [K]; linear_combination hhZ
    have hhW' : K*L.w 0=0 := by
      simp [A,hw1,hw2] at hhW
      dsimp [K]; linear_combination hhW
    exact ⟨(mul_eq_zero.mp hhZ').resolve_left hK,(mul_eq_zero.mp hhW').resolve_left hK⟩
  · intro h03 h34'
    have hA : ∀ i∈({3}:Finset (Fin 5)), ∀ j∈({3}:Finset (Fin 5))ᶜ,
        (L.z i-L.z j)*(L.w i-L.w j) ≠ 0 := by
      intro i hi j hj
      simp only [Finset.mem_singleton] at hi
      subst i
      have hj3 : j ≠ 3 := by simpa using hj
      by_cases hjt : j<3
      · rw [hz j hjt,hw j hjt]
        convert h03 using 1 <;> ring
      · have hj4 : j=4 := by omega
        subst j
        exact h34'
    have hhZ := L.isolated_block_z hs hr hprod {3} hA
    have hhW := L.isolated_block_w hs hr hprod {3} hA
    exact ⟨by simpa [h3] using hhZ,by simpa [h3] using hhW⟩
  · intro h04 h34'
    have hA : ∀ i∈({4}:Finset (Fin 5)), ∀ j∈({4}:Finset (Fin 5))ᶜ,
        (L.z i-L.z j)*(L.w i-L.w j) ≠ 0 := by
      intro i hi j hj
      simp only [Finset.mem_singleton] at hi
      subst i
      have hj4 : j ≠ 4 := by simpa using hj
      by_cases hjt : j<3
      · rw [hz j hjt,hw j hjt]
        convert h04 using 1 <;> ring
      · have hj3 : j=3 := by omega
        subst j
        convert h34' using 1 <;> ring
    have hhZ := L.isolated_block_z hs hr hprod {4} hA
    have hhW := L.isolated_block_w hs hr hprod {4} hA
    exact ⟨by simpa [h4] using hhZ,by simpa [h4] using hhW⟩

end CentralConfigurations.FiveBody.D5
