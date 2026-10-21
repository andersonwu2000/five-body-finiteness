import CentralConfigurations.Asymptotics.KiteRatioLimits
import CentralConfigurations.Diagrams.TwoRowTriangleMass

/-!
# Three closed rows in a fully edged triangle

Two zero-position rows in one color and the first zero-position row in the
other color suffice. The second force ratio is forced by the two separation
identities for one common subsequence. The remaining row may have external
leading forces. This supplies the triangle factors used in Section 11.5.
-/

namespace CentralConfigurations

open Filter
open scoped Topology

theorem ScaledZWLimit.three_uncircled_triangle_rows_mass_polynomial
    {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun a => (mass a : ℂ))} {scale : ℕ → ℂ}
    (l : ScaledZWLimit q scale) (hscale : ∀ t, scale t ≠ 0)
    (hm : ∀ a, 0 < mass a) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzi : l.z.position i = 0) (hzj : l.z.position j = 0)
    (hwi : l.w.position i = 0)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j ≠ 0)
    (hwjk : l.w.force j k ≠ 0)
    (hzci : ∀ r, r ≠ j → r ≠ k → l.z.force i r = 0)
    (hzcj : ∀ r, r ≠ i → r ≠ k → l.z.force j r = 0)
    (hwci : ∀ r, r ≠ j → r ≠ k → l.w.force i r = 0) :
    triangleMassPolynomial (mass i) (mass j) (mass k) = 0 := by
  have hmi : (mass i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm i))
  have hmj : (mass j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm j))
  have hmk : (mass k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm k))
  have hzrat := l.z.two_term_force_ratios i j k hik hjk hmk hz hzi hzj hzci hzcj
  have hwr : l.w.force i k / l.w.force i j = -(mass j : ℂ) / (mass k : ℂ) := by
    have hb := l.w.two_term_balance i j k hjk hwi hwci
    field_simp [hw, hmk]
    linear_combination hb
  have hzik := tendsto_ratio_of_scaled hscale hz (l.z_force i k) (l.z_force i j)
  have hwik := tendsto_ratio_of_scaled hscale hw (l.w_force i k) (l.w_force i j)
  have hzjk := tendsto_ratio_of_scaled hscale hz (l.z_force j k) (l.z_force i j)
  have hwjklim := tendsto_ratio_of_scaled hscale hw (l.w_force j k) (l.w_force i j)
  rw [hzrat.1] at hzik
  rw [hwr] at hwik
  rw [hzrat.2] at hzjk
  have hu : -(mass j : ℂ) / (mass k : ℂ) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hmj) hmk
  have hv : (mass i : ℂ) / (mass k : ℂ) ≠ 0 := div_ne_zero hmi hmk
  have hV := div_ne_zero hwjk hw
  obtain ⟨x, y, hx, hy, hsz, hsw⟩ := two_color_triangle_force_ratio_roots q i j k hij hik hjk
    (-(mass j : ℂ) / (mass k : ℂ)) ((mass i : ℂ) / (mass k : ℂ))
    (-(mass j : ℂ) / (mass k : ℂ)) (l.w.force j k / l.w.force i j)
    hu hv hu hV hzik hwik hzjk hwjklim
  have hyne : y ≠ 0 := by
    intro hy0
    rw [hy0, zero_pow (by decide : 4 ≠ 0)] at hy
    exact (mul_ne_zero hv hV) hy.symm
  have hdiv : y / (l.w.force j k / l.w.force i j) = y / ((mass i : ℂ) / (mass k : ℂ)) := by
    linear_combination hsw - hsz
  have hVv : l.w.force j k / l.w.force i j = (mass i : ℂ) / (mass k : ℂ) := by
    field_simp [hV, hv] at hdiv
    field_simp [hw, hmk]
    linear_combination -hdiv
  rw [hVv] at hy
  exact triangle_mass_polynomial_of_roots (mass i) (mass j) (mass k)
    (hm i) (hm j) (hm k) x y (by simpa only [pow_two] using hx)
    (by simpa only [pow_two] using hy) hsw

theorem ScaledZWLimit.three_uncircled_triangle_rows_of_code
    {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    {d : DiagramCode n} (hd : l.diagramCode = d)
    (hm : ∀ a, 0 < mass a) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hdiag : d.1 (upperIndex i i) = false ∧ d.1 (upperIndex j j) = false ∧
      d.2 (upperIndex i i) = false)
    (hedge : d.1 (upperIndex i j) = true ∧ d.2 (upperIndex i j) = true ∧
      d.2 (upperIndex j k) = true)
    (hci : ∀ r, r ≠ j → r ≠ k →
      d.1 (upperIndex i r) = false ∧ d.2 (upperIndex i r) = false)
    (hcj : ∀ r, r ≠ i → r ≠ k → d.1 (upperIndex j r) = false) :
    triangleMassPolynomial (mass i) (mass j) (mass k) = 0 :=
  l.three_uncircled_triangle_rows_mass_polynomial
    (ScaledZWLimit.inverseScale_ne_zero (q := q) i j hij) hm i j k hij hik hjk
    (l.z_position_zero_of_code hd i hdiag.1)
    (l.z_position_zero_of_code hd j hdiag.2.1)
    (l.w_position_zero_of_code hd i hdiag.2.2)
    (l.z_force_ne_zero_of_code hd i j hij hedge.1)
    (l.w_force_ne_zero_of_code hd i j hij hedge.2.1)
    (l.w_force_ne_zero_of_code hd j k hjk hedge.2.2)
    (fun r hrj hrk => l.z_force_zero_of_code hd i r (hci r hrj hrk).1)
    (fun r hri hrk => l.z_force_zero_of_code hd j r (hcj r hri hrk))
    (fun r hrj hrk => l.w_force_zero_of_code hd i r (hci r hrj hrk).2)

theorem ScaledZWLimit.three_uncircled_triangle_rows_swapped_of_code
    {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    {d : DiagramCode n} (hd : l.diagramCode = d)
    (hm : ∀ a, 0 < mass a) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hdiag : d.2 (upperIndex i i) = false ∧ d.2 (upperIndex j j) = false ∧
      d.1 (upperIndex i i) = false)
    (hedge : d.2 (upperIndex i j) = true ∧ d.1 (upperIndex i j) = true ∧
      d.1 (upperIndex j k) = true)
    (hci : ∀ r, r ≠ j → r ≠ k →
      d.2 (upperIndex i r) = false ∧ d.1 (upperIndex i r) = false)
    (hcj : ∀ r, r ≠ i → r ≠ k → d.2 (upperIndex j r) = false) :
    triangleMassPolynomial (mass i) (mass j) (mass k) = 0 :=
  l.swap.three_uncircled_triangle_rows_mass_polynomial
    (ScaledZWLimit.inverseScale_ne_zero (q := q) i j hij) hm i j k hij hik hjk
    (l.w_position_zero_of_code hd i hdiag.1)
    (l.w_position_zero_of_code hd j hdiag.2.1)
    (l.z_position_zero_of_code hd i hdiag.2.2)
    (l.w_force_ne_zero_of_code hd i j hij hedge.1)
    (l.z_force_ne_zero_of_code hd i j hij hedge.2.1)
    (l.z_force_ne_zero_of_code hd j k hjk hedge.2.2)
    (fun r hrj hrk => l.w_force_zero_of_code hd i r (hci r hrj hrk).1)
    (fun r hri hrk => l.w_force_zero_of_code hd j r (hcj r hri hrk))
    (fun r hrj hrk => l.z_force_zero_of_code hd i r (hci r hrj hrk).2)

end CentralConfigurations
