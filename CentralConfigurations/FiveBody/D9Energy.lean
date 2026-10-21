import CentralConfigurations.FiveBody.D9Sequence
import CentralConfigurations.FiveBody.D9Mass

namespace CentralConfigurations.FiveBody.D9
open Filter
open scoped Topology BigOperators

theorem norm_cube_limit {f : ℕ → ℂ} {r : ℝ} (hr : 0 ≤ r)
    (h : Tendsto (fun t => f t ^ 3) atTop (𝓝 (r : ℂ))) :
    Tendsto (fun t => ‖f t‖) atTop (𝓝 (cubeRoot r)) := by
  have hc : Continuous cubeRoot := Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1/3)
  have hh := (hc.tendsto ‖(r : ℂ)‖).comp h.norm
  convert hh using 1
  · funext t
    dsimp only [Function.comp_apply]
    rw [norm_pow]
    simpa [cubeRoot, one_div] using (Real.pow_rpow_inv_natCast (norm_nonneg (f t)) (by decide : (3 : ℕ) ≠ 0)).symm
  · simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}

theorem full_potential_norm_le (q : ZWSystem ℂ 5 mass) :
    ‖q.toNormalized.unorderedPotential‖ ≤
      ‖triplePotential q‖ + ‖mass 0 * mass 3 * q.delta 0 3‖ +
      ‖mass 0 * mass 4 * q.delta 0 4‖ + ‖mass 1 * mass 3 * q.delta 1 3‖ +
      ‖mass 1 * mass 4 * q.delta 1 4‖ + ‖mass 2 * mass 3 * q.delta 2 3‖ +
      ‖mass 2 * mass 4 * q.delta 2 4‖ + ‖mass 3 * mass 4 * q.delta 3 4‖ := by
  have h := norm_sum_le Finset.univ
    (![triplePotential q, mass 0 * mass 3 * q.delta 0 3,
      mass 0 * mass 4 * q.delta 0 4, mass 1 * mass 3 * q.delta 1 3,
      mass 1 * mass 4 * q.delta 1 4, mass 2 * mass 3 * q.delta 2 3,
      mass 2 * mass 4 * q.delta 2 4, mass 3 * mass 4 * q.delta 3 4] : Fin 8 → ℂ)
  rw [potential_decomposition]
  simpa [Fin.sum_univ_succ, exteriorPotential, add_assoc] using h

/-- Complete phase-uniform energy bound.  The four disappearing edges and
the whole internal triple are included before applying the triangle inequality. -/
theorem complete_energy_bound {m : Fin 5 → ℝ} (hm : ∀ i, 0 < m i)
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))} {I0 A B C : ℝ}
    (hI : ∀ t, (q t).toNormalized.unorderedPotential = (I0 : ℂ))
    (htr : Tendsto (fun t => triplePotential (q t)) atTop (𝓝 0))
    (h04 : Tendsto (fun t => (q t).delta 0 4) atTop (𝓝 0))
    (h13 : Tendsto (fun t => (q t).delta 1 3) atTop (𝓝 0))
    (h23 : Tendsto (fun t => (q t).delta 2 3) atTop (𝓝 0))
    (h24 : Tendsto (fun t => (q t).delta 2 4) atTop (𝓝 0))
    (h03 : Tendsto (fun t => ‖(q t).delta 0 3‖) atTop (𝓝 A))
    (h14 : Tendsto (fun t => ‖(q t).delta 1 4‖) atTop (𝓝 B))
    (h34 : Tendsto (fun t => ‖(q t).delta 3 4‖) atTop (𝓝 C)) :
    |I0| ≤ m 0*m 3*A + m 1*m 4*B + m 3*m 4*C := by
  have normmass (i : Fin 5) : ‖(m i : ℂ)‖ = m i := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hm i)]
  have term {i j : Fin 5} {L : ℝ}
      (hd : Tendsto (fun t => ‖(q t).delta i j‖) atTop (𝓝 L)) :
      Tendsto (fun t => ‖(m i : ℂ)*(m j : ℂ)*(q t).delta i j‖) atTop
        (𝓝 (m i*m j*L)) := by
    simpa only [norm_mul, normmass] using hd.const_mul (m i*m j)
  have ht := (((((((htr.norm.add (term h03)).add (term h04.norm)).add
    (term h13.norm)).add (term h14)).add (term h23.norm)).add (term h24.norm)).add (term h34))
  simp only [norm_zero, mul_zero, zero_add, add_zero] at ht
  apply ge_of_tendsto ht
  filter_upwards [] with t
  have hn := full_potential_norm_le (q t)
  simpa only [hI, Complex.norm_real, Real.norm_eq_abs] using hn

/-- Exact physical floor contradicts the complete maximal-attachment energy
limit.  No limit inverse is required to lie on the positive real sheet. -/
theorem false_of_complete_cube_limits {m : Fin 5 → ℝ} (hm : ∀ i, 0 < m i)
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))} {I0 : ℝ}
    (hIpos : 0 < I0)
    (hfloor : ((m 0*m 1+m 0*m 2+m 1*m 2)+
      (m 0+m 1+m 2)*(m 3+m 4)+m 3*m 4)^3 ≤
      (m 0+m 1+m 2+m 3+m 4)*I0^3)
    (hI : ∀ t, (q t).toNormalized.unorderedPotential = (I0 : ℂ))
    (htr : Tendsto (fun t => triplePotential (q t)) atTop (𝓝 0))
    (h04 : Tendsto (fun t => (q t).delta 0 4) atTop (𝓝 0))
    (h13 : Tendsto (fun t => (q t).delta 1 3) atTop (𝓝 0))
    (h23 : Tendsto (fun t => (q t).delta 2 3) atTop (𝓝 0))
    (h24 : Tendsto (fun t => (q t).delta 2 4) atTop (𝓝 0))
    (h03 : Tendsto (fun t => (q t).delta 0 3^3) atTop
      (𝓝 (((m 0+m 1+m 2)/((m 0+m 1+m 2+m 3+m 4)*m 0) : ℝ) : ℂ)))
    (h14 : Tendsto (fun t => (q t).delta 1 4^3) atTop
      (𝓝 (((m 0+m 1+m 2)/((m 0+m 1+m 2+m 3+m 4)*m 1) : ℝ) : ℂ)))
    (h34 : Tendsto (fun t => (q t).delta 3 4^3) atTop
      (𝓝 (((1/(m 3+m 4)) : ℝ) : ℂ))) : False := by
  have h0 := hm 0
  have h1 := hm 1
  have h2 := hm 2
  have h3 := hm 3
  have h4 := hm 4
  let K := m 0+m 1+m 2
  let M := m 0+m 1+m 2+m 3+m 4
  let P := m 3+m 4
  have hK : 0 < K := by dsimp [K]; positivity
  have hM : 0 < M := by dsimp [M]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have henergy := complete_energy_bound hm hI htr h04 h13 h23 h24
    (norm_cube_limit (by positivity) h03)
    (norm_cube_limit (by positivity) h14)
    (norm_cube_limit (by positivity) h34)
  rw [abs_of_pos hIpos] at henergy
  have hh := mul_le_mul_of_nonneg_left henergy (cubeRoot_pos hM).le
  have hscaled : cubeRoot M*I0 ≤
      cubeRoot K*(m 3*cubeRoot (m 0)^2+m 4*cubeRoot (m 1)^2)+
      m 3*m 4*cubeRoot (M/P) := by
    convert hh using 1
    symm
    calc
      _ = m 3*(cubeRoot M*m 0*cubeRoot (K/(M*m 0))) +
          m 4*(cubeRoot M*m 1*cubeRoot (K/(M*m 1))) +
          m 3*m 4*(cubeRoot M*cubeRoot (1/P)) := by dsimp [K, M, P]; ring
      _ = _ := by
        rw [scaled_attachment_root hM hK.le (hm 0),
          scaled_attachment_root hM hK.le (hm 1), scaled_outer_root hM.le hP]
        ring
  have hgap := scaled_envelope_lt (hm 0) (hm 1) (hm 2) (hm 3) (hm 4)
  have hlt := hscaled.trans_lt hgap
  have hcub := (Odd.strictMono_pow (by decide : Odd 3)) hlt
  dsimp only at hcub
  rw [mul_pow, cubeRoot_cube hM.le] at hcub
  exact (not_lt_of_ge hfloor) hcub

end CentralConfigurations.FiveBody.D9

