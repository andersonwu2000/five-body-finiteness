import CentralConfigurations.Algebra.TriangleMass
import CentralConfigurations.Asymptotics.TriangleRatioLimits
import CentralConfigurations.Diagrams.ComponentMassRelations

/-!
# The two uncircled rows in the fully edged triangle

Sections 9.2 and 11.3. Two rows have zero leading position in both colors and
no external leading force. Their balance ratios, the branch-preserving distance
identities, and positive masses imply the triangle mass polynomial. The third
vertex may have arbitrary external strokes.
-/

namespace CentralConfigurations

open Filter
open scoped Topology BigOperators

theorem OneColorLimit.two_term_balance {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (i j k : Fin n) (hjk : j ≠ k)
    (hi : q.position i = 0)
    (hother : ∀ r, r ≠ j → r ≠ k → q.force i r = 0) :
    mass j * q.force i j + mass k * q.force i k = 0 := by
  classical
  have hsum : (∑ r, mass r * q.force i r) =
      ∑ r ∈ ({j, k} : Finset (Fin n)), mass r * q.force i r := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro r _ hr
    have hri : r ≠ j ∧ r ≠ k := by simpa using hr
    rw [hother r hri.1 hri.2, mul_zero]
  have h := q.balance i
  rw [hi, hsum, Finset.sum_pair hjk] at h
  exact h.symm

theorem OneColorLimit.two_term_force_ratios {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (i j k : Fin n) (hik : i ≠ k) (hjk : j ≠ k)
    (hm : mass k ≠ 0) (hf : q.force i j ≠ 0)
    (hi : q.position i = 0) (hj : q.position j = 0)
    (hci : ∀ r, r ≠ j → r ≠ k → q.force i r = 0)
    (hcj : ∀ r, r ≠ i → r ≠ k → q.force j r = 0) :
    q.force i k / q.force i j = -mass j / mass k ∧
      q.force j k / q.force i j = mass i / mass k := by
  have hA := q.two_term_balance i j k hjk hi hci
  have hB := q.two_term_balance j i k hik hj hcj
  rw [q.antisymm j i] at hB
  constructor
  · field_simp [hf, hm]
    linear_combination hA
  · field_simp [hf, hm]
    linear_combination hB

theorem ScaledZWLimit.two_uncircled_triangle_rows_mass_polynomial
    {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ a, 0 < mass a) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hzi : l.z.position i = 0) (hzj : l.z.position j = 0)
    (hwi : l.w.position i = 0) (hwj : l.w.position j = 0)
    (hz : l.z.force i j ≠ 0) (hw : l.w.force i j ≠ 0)
    (hzci : ∀ r, r ≠ j → r ≠ k → l.z.force i r = 0)
    (hzcj : ∀ r, r ≠ i → r ≠ k → l.z.force j r = 0)
    (hwci : ∀ r, r ≠ j → r ≠ k → l.w.force i r = 0)
    (hwcj : ∀ r, r ≠ i → r ≠ k → l.w.force j r = 0) :
    triangleMassPolynomial (mass i) (mass j) (mass k) = 0 := by
  have hmk : (mass k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (hm k))
  have hzrat := l.z.two_term_force_ratios i j k hik hjk hmk hz hzi hzj hzci hzcj
  have hwrat := l.w.two_term_force_ratios i j k hik hjk hmk hw hwi hwj hwci hwcj
  have hscale := ScaledZWLimit.inverseScale_ne_zero (q := q) i j hij
  have hzik := tendsto_ratio_of_scaled hscale hz (l.z_force i k) (l.z_force i j)
  have hwik := tendsto_ratio_of_scaled hscale hw (l.w_force i k) (l.w_force i j)
  have hzjk := tendsto_ratio_of_scaled hscale hz (l.z_force j k) (l.z_force i j)
  have hwjk := tendsto_ratio_of_scaled hscale hw (l.w_force j k) (l.w_force i j)
  rw [hzrat.1] at hzik
  rw [hwrat.1] at hwik
  rw [hzrat.2] at hzjk
  rw [hwrat.2] at hwjk
  have hu : -(mass j : ℂ) / (mass k : ℂ) ≠ 0 :=
    div_ne_zero (neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (ne_of_gt (hm j)))) hmk
  have hv : (mass i : ℂ) / (mass k : ℂ) ≠ 0 :=
    div_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt (hm i))) hmk
  obtain ⟨x, y, hx, hy, hs⟩ := triangle_force_ratio_roots q i j k hij hik hjk
    (-(mass j : ℂ) / (mass k : ℂ)) ((mass i : ℂ) / (mass k : ℂ)) hu hv hzik hwik hzjk hwjk
  exact triangle_mass_polynomial_of_roots (mass i) (mass j) (mass k)
    (hm i) (hm j) (hm k) x y hx hy hs

theorem ScaledZWLimit.two_uncircled_triangle_rows_of_code
    {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun a => (mass a : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    {d : DiagramCode n} (hd : l.diagramCode = d)
    (hm : ∀ a, 0 < mass a) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hdiag : d.1 (upperIndex i i) = false ∧ d.1 (upperIndex j j) = false ∧
      d.2 (upperIndex i i) = false ∧ d.2 (upperIndex j j) = false)
    (hedge : d.1 (upperIndex i j) = true ∧ d.2 (upperIndex i j) = true)
    (hci : ∀ r, r ≠ j → r ≠ k →
      d.1 (upperIndex i r) = false ∧ d.2 (upperIndex i r) = false)
    (hcj : ∀ r, r ≠ i → r ≠ k →
      d.1 (upperIndex j r) = false ∧ d.2 (upperIndex j r) = false) :
    triangleMassPolynomial (mass i) (mass j) (mass k) = 0 :=
  l.two_uncircled_triangle_rows_mass_polynomial hm i j k hij hik hjk
    (l.z_position_zero_of_code hd i hdiag.1)
    (l.z_position_zero_of_code hd j hdiag.2.1)
    (l.w_position_zero_of_code hd i hdiag.2.2.1)
    (l.w_position_zero_of_code hd j hdiag.2.2.2)
    (l.z_force_ne_zero_of_code hd i j hij hedge.1)
    (l.w_force_ne_zero_of_code hd i j hij hedge.2)
    (fun r hrj hrk => l.z_force_zero_of_code hd i r (hci r hrj hrk).1)
    (fun r hri hrk => l.z_force_zero_of_code hd j r (hcj r hri hrk).1)
    (fun r hrj hrk => l.w_force_zero_of_code hd i r (hci r hrj hrk).2)
    (fun r hri hrk => l.w_force_zero_of_code hd j r (hcj r hri hrk).2)

end CentralConfigurations
