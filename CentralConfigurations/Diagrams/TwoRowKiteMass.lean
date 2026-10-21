import CentralConfigurations.Algebra.KiteElimination
import CentralConfigurations.Asymptotics.KiteRatioLimits
import CentralConfigurations.Diagrams.TwoRowTriangleMass

/-!
# Two-row kite mass equations from an actual singular limit

Two closed rows have zero z position and equal w position. Their z force
ratios and w force difference retain both separation triangles on one common
subsequence. The polynomial identity then eliminates the complex ratio.
-/

namespace CentralConfigurations

open Filter
open scoped Topology BigOperators

theorem OneColorLimit.two_term_position {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (i j k : Fin n) (hjk : j ≠ k)
    (hother : ∀ r, r ≠ j → r ≠ k → q.force i r = 0) :
    q.position i = mass j * q.force i j + mass k * q.force i k := by
  classical
  have hsum : (∑ r, mass r * q.force i r) =
      ∑ r ∈ ({j, k} : Finset (Fin n)), mass r * q.force i r := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro r _ hr
    have hri : r ≠ j ∧ r ≠ k := by simpa using hr
    rw [hother r hri.1 hri.2, mul_zero]
  have h := q.balance i
  rwa [hsum, Finset.sum_pair hjk] at h

theorem OneColorLimit.two_equal_positions_force_difference {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k)
    (hm : mass k ≠ 0) (hf : q.force i j ≠ 0)
    (hp : q.position i = q.position j)
    (hci : ∀ r, r ≠ j → r ≠ k → q.force i r = 0)
    (hcj : ∀ r, r ≠ i → r ≠ k → q.force j r = 0) :
    q.force j k / q.force i j - q.force i k / q.force i j =
      (mass i + mass j) / mass k := by
  have hA := q.two_term_position i j k hjk hci
  have hB := q.two_term_position j i k hik hcj
  rw [q.antisymm j i] at hB
  field_simp [hf, hm]
  linear_combination hA - hB - hp

theorem ScaledZWLimit.two_kite_rows_mass_polynomial
    {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ a, 0 < mass a) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzi : l.z.position i = 0) (hzj : l.z.position j = 0)
    (hwij : l.w.position i = l.w.position j)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j ≠ 0)
    (hwik : l.w.force i k ≠ 0) (hwjk : l.w.force j k ≠ 0)
    (hzci : ∀ r, r ≠ j → r ≠ k → l.z.force i r = 0)
    (hzcj : ∀ r, r ≠ i → r ≠ k → l.z.force j r = 0)
    (hwci : ∀ r, r ≠ j → r ≠ k → l.w.force i r = 0)
    (hwcj : ∀ r, r ≠ i → r ≠ k → l.w.force j r = 0) :
    kiteMassPolynomial (mass i) (mass j) (mass k) = 0 := by
  have hmi : (mass i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm i))
  have hmj : (mass j : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm j))
  have hmk : (mass k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm k))
  have hzrat := l.z.two_term_force_ratios i j k hik hjk hmk hz hzi hzj hzci hzcj
  have hwrat := l.w.two_equal_positions_force_difference i j k hik hjk hmk hw hwij hwci hwcj
  have hscale := ScaledZWLimit.inverseScale_ne_zero (q := q) i j hij
  have hzik := tendsto_ratio_of_scaled hscale hz (l.z_force i k) (l.z_force i j)
  have hwiklim := tendsto_ratio_of_scaled hscale hw (l.w_force i k) (l.w_force i j)
  have hzjk := tendsto_ratio_of_scaled hscale hz (l.z_force j k) (l.z_force i j)
  have hwjklim := tendsto_ratio_of_scaled hscale hw (l.w_force j k) (l.w_force i j)
  rw [hzrat.1] at hzik
  rw [hzrat.2] at hzjk
  have hu : -(mass j : ℂ) / (mass k : ℂ) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hmj) hmk
  have hv : (mass i : ℂ) / (mass k : ℂ) ≠ 0 := div_ne_zero hmi hmk
  have hU := div_ne_zero hwik hw
  have hV := div_ne_zero hwjk hw
  obtain ⟨x, y, hx, hy, hsz, hsw⟩ := two_color_triangle_force_ratio_roots q i j k hij hik hjk
    (-(mass j : ℂ) / (mass k : ℂ)) ((mass i : ℂ) / (mass k : ℂ))
    (l.w.force i k / l.w.force i j) (l.w.force j k / l.w.force i j)
    hu hv hU hV hzik hwiklim hzjk hwjklim
  obtain ⟨t, hF, hG⟩ := kite_equations_of_roots (mass i : ℂ) (mass j : ℂ) (mass k : ℂ)
    x y (l.w.force i k / l.w.force i j) (l.w.force j k / l.w.force i j)
    hmi hmj hmk hU hV hx hy hsz hsw hwrat
  exact kite_mass_polynomial_of_equations (mass i) (mass j) (mass k) (hm i) (hm j) (hm k) t hF hG

theorem ScaledZWLimit.two_kite_rows_of_code
    {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    {d : DiagramCode n} (hd : l.diagramCode = d)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hm : ∀ a, 0 < mass a) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hdiag : d.1 (upperIndex i i) = false ∧ d.1 (upperIndex j j) = false)
    (hedge : d.1 (upperIndex i j) = true ∧ d.2 (upperIndex i j) = true ∧
      d.2 (upperIndex i k) = true ∧ d.2 (upperIndex j k) = true)
    (hci : ∀ r, r ≠ i → r ≠ j → r ≠ k →
      d.1 (upperIndex i r) = false ∧ d.2 (upperIndex i r) = false)
    (hcj : ∀ r, r ≠ j → r ≠ i → r ≠ k →
      d.1 (upperIndex j r) = false ∧ d.2 (upperIndex j r) = false) :
    kiteMassPolynomial (mass i) (mass j) (mass k) = 0 := by
  apply l.two_kite_rows_mass_polynomial hm i j k hij hik hjk
    (l.z_position_zero_of_code hd i hdiag.1)
    (l.z_position_zero_of_code hd j hdiag.2)
    (l.w_position_eq_of_z_code_edge hd ha i j hij hedge.1)
    (l.z_force_ne_zero_of_code hd i j hij hedge.1)
    (l.w_force_ne_zero_of_code hd i j hij hedge.2.1)
    (l.w_force_ne_zero_of_code hd i k hik hedge.2.2.1)
    (l.w_force_ne_zero_of_code hd j k hjk hedge.2.2.2)
  · intro r hrj hrk
    by_cases hri : r = i
    · subst r; exact l.z.diagonal i
    · exact l.z_force_zero_of_code hd i r (hci r hri hrj hrk).1
  · intro r hri hrk
    by_cases hrj : r = j
    · subst r; exact l.z.diagonal j
    · exact l.z_force_zero_of_code hd j r (hcj r hrj hri hrk).1
  · intro r hrj hrk
    by_cases hri : r = i
    · subst r; exact l.w.diagonal i
    · exact l.w_force_zero_of_code hd i r (hci r hri hrj hrk).2
  · intro r hri hrk
    by_cases hrj : r = j
    · subst r; exact l.w.diagonal j
    · exact l.w_force_zero_of_code hd j r (hcj r hrj hri hrk).2

end CentralConfigurations
