import CentralConfigurations.FiveBody.D2Actual.CommonExtraction
import CentralConfigurations.FiveBody.D2Actual.MassEnvelope
import CentralConfigurations.FiveBody.PhysicalPotentialFloor
import CentralConfigurations.ThreeBody.Classification

namespace CentralConfigurations.FiveBody.D2
open Filter D9
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

theorem norm_of_cube_inverse {d : ℂ} {A : ℝ} (hA : 0 < A)
    (hd : d^3 = (A : ℂ)⁻¹) : ‖d‖ = 1/cubeRoot A := by
  apply cube_inj
  have hn : ‖d‖^3 = A⁻¹ := by
    rw [← norm_pow, hd, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hA]
  rw [div_pow, one_pow, cubeRoot_cube hA.le]
  simpa only [one_div] using hn

theorem ActualLimit.false_of_triangle_envelope {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
    (s : ActualLimit m q l (I0 : ℂ)) (hm : ∀ i, 0 < m i)
    (hphysical : PhysicalPotentialLevel m I0)
    (hQ : ‖s.triangle.toNormalized.potential‖ ≤
      (m 0*m 1+m 0*m 2+m 1*m 2)/cubeRoot (m 0+m 1+m 2)) : False := by
  have hA : 0 < m 3+m 4 := add_pos (hm 3) (hm 4)
  have hB : 0 < m 0+m 1+m 2 := add_pos (add_pos (hm 0) (hm 1)) (hm 2)
  have hM : 0 < m 0+m 1+m 2+m 3+m 4 := add_pos (add_pos hB (hm 3)) (hm 4)
  have hnD : ‖s.pairDelta‖ = 1/cubeRoot (m 3+m 4) :=
    norm_of_cube_inverse hA (by simpa only [Complex.ofReal_add] using s.pair_delta_cube)
  have hnp : ‖(m 3 : ℂ)*m 4*s.pairDelta‖ = m 3*m 4/cubeRoot (m 3+m 4) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos (hm 3), abs_of_pos (hm 4), hnD]
    ring
  have hnI : I0 ≤ m 3*m 4/cubeRoot (m 3+m 4) +
      (m 0*m 1+m 0*m 2+m 1*m 2)/cubeRoot (m 0+m 1+m 2) := by
    have h := norm_add_le ((m 3 : ℂ)*m 4*s.pairDelta) s.triangle.toNormalized.potential
    rw [s.potential_split, hnp, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hphysical.1] at h
    linarith
  have hbound := mul_le_mul_of_nonneg_left hnI (cubeRoot_pos hM).le
  have hgap := five_mass_envelope_gap hm
  have hsmall : cubeRoot (totalMass m)*I0 < pairMassSum m := by
    have hS : pairMassSum m =
        m 3*m 4+(m 0*m 1+m 0*m 2+m 1*m 2)+(m 3+m 4)*(m 0+m 1+m 2) := by
      simp [pairMassSum, Fin.sum_univ_succ]
      ring
    have htotal : totalMass m = m 0+m 1+m 2+m 3+m 4 := by
      simp [totalMass, Fin.sum_univ_succ]; ring
    rw [hS, htotal]
    exact lt_of_le_of_lt hbound hgap
  have hsmallCube := (Odd.strictMono_pow (by decide : Odd 3)) hsmall
  dsimp only at hsmallCube
  rw [mul_pow, cubeRoot_cube (by simpa [totalMass, Fin.sum_univ_succ, add_assoc] using hM.le)]
    at hsmallCube
  exact (not_lt_of_ge hphysical.2) hsmallCube

theorem triangle_envelope_of_equal_cube {m : Fin 5 → ℝ}
    (r : ZWSystem ℂ 3 (fun i => (m (i.castLE (by decide)) : ℂ)))
    (hm : ∀ i, 0 < m i)
    (hcube : ∀ i j, i ≠ j → ((m 0 : ℂ)+m 1+m 2)*r.delta i j^3 = 1) :
    ‖r.toNormalized.potential‖ ≤
      (m 0*m 1+m 0*m 2+m 1*m 2)/cubeRoot (m 0+m 1+m 2) := by
  have hB : 0 < m 0+m 1+m 2 := add_pos (add_pos (hm 0) (hm 1)) (hm 2)
  have hBC : (m 0 : ℂ)+m 1+m 2 ≠ 0 := by exact_mod_cast ne_of_gt hB
  have hn (i j : Fin 3) (hij : i ≠ j) :
      ‖r.delta i j‖ = 1/cubeRoot (m 0+m 1+m 2) := by
    apply norm_of_cube_inverse hB
    have h := hcube i j hij
    have hd : r.delta i j^3 = ((m 0 : ℂ)+m 1+m 2)⁻¹ := by
      apply (mul_left_cancel₀ hBC)
      rw [h, mul_inv_cancel₀ hBC]
    simpa only [Complex.ofReal_add] using hd
  rw [three_potential]
  have h := (norm_add_le
    ((m 0 : ℂ)*m 1*r.delta 0 1+(m 0 : ℂ)*m 2*r.delta 0 2)
    ((m 1 : ℂ)*m 2*r.delta 1 2)).trans
    (add_le_add (norm_add_le ((m 0 : ℂ)*m 1*r.delta 0 1)
      ((m 0 : ℂ)*m 2*r.delta 0 2)) le_rfl)
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hm 0),
    abs_of_pos (hm 1), abs_of_pos (hm 2), hn 0 1 (by decide),
    hn 0 2 (by decide), hn 1 2 (by decide)] at h
  convert h using 1
  ring

theorem ActualLimit.false_of_equal_cube {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
    (s : ActualLimit m q l (I0 : ℂ)) (hm : ∀ i, 0 < m i)
    (hphysical : PhysicalPotentialLevel m I0)
    (hcube : ∀ i j, i ≠ j → ((m 0 : ℂ)+m 1+m 2)*s.triangle.delta i j^3 = 1) : False :=
  s.false_of_triangle_envelope hm hphysical (triangle_envelope_of_equal_cube s.triangle hm hcube)

theorem ActualLimit.false_of_triangle_potential_zero {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
    (s : ActualLimit m q l (I0 : ℂ)) (hm : ∀ i, 0 < m i)
    (hphysical : PhysicalPotentialLevel m I0) (hQ : s.triangle.toNormalized.potential = 0) :
    False := by
  apply s.false_of_triangle_envelope hm hphysical
  rw [hQ, norm_zero]
  apply div_nonneg
  · exact add_nonneg
      (add_nonneg (mul_pos (hm 0) (hm 1)).le (mul_pos (hm 0) (hm 2)).le)
      (mul_pos (hm 1) (hm 2)).le
  · exact (cubeRoot_pos (add_pos (add_pos (hm 0) (hm 1)) (hm 2))).le

theorem ActualLimit.triangle_area_zero {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
    (s : ActualLimit m q l (I0 : ℂ)) (hm : ∀ i, 0 < m i)
    (hphysical : PhysicalPotentialLevel m I0) : threeBodyArea s.triangle = 0 := by
  rcases s.triangle.three_body_euler_or_lagrange
    (fun i => Complex.ofReal_ne_zero.mpr (ne_of_gt (hm (i.castLE (by decide))))) with h | h
  · exact h
  · exact False.elim (s.false_of_equal_cube hm hphysical h)

end CentralConfigurations.FiveBody.D2
