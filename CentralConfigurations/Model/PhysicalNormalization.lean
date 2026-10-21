import CentralConfigurations.Model.RealGauge
import CentralConfigurations.Model.Virial
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Positive-multiplier and scale normalization of the real equations

This is the real system in Section 2.1 before setting the multiplier to one.
Positive off-diagonal inverse distances distinguish the Newtonian branch.
The multiplier's positivity is proved from the equations, not assumed.
-/

namespace CentralConfigurations

open scoped BigOperators

structure RealCentralSystem (n : ℕ) (mass : Fin n → ℝ) where
  x : Fin n → ℝ
  y : Fin n → ℝ
  delta : Fin n → Fin n → ℝ
  multiplier : ℝ
  delta_symm : ∀ i j, delta i j = delta j i
  delta_diagonal : ∀ i, delta i i = 0
  delta_pos : ∀ i j, i ≠ j → 0 < delta i j
  force_x : ∀ i, multiplier * x i = ∑ j, mass j * delta i j ^ 3 * (x i - x j)
  force_y : ∀ i, multiplier * y i = ∑ j, mass j * delta i j ^ 3 * (y i - y j)
  distance : ∀ i j, i ≠ j → delta i j ^ 2 * squaredSeparation x y i j = 1

namespace RealCentralSystem

variable {n : ℕ} {mass : Fin n → ℝ} (q : RealCentralSystem n mass)

def inertia : ℝ := ∑ i, mass i * (q.x i ^ 2 + q.y i ^ 2)
def doubledPotential : ℝ := ∑ i, ∑ j, mass i * mass j * q.delta i j

theorem delta_nonneg (i j : Fin n) : 0 ≤ q.delta i j := by
  by_cases h : i = j
  · subst j; rw [q.delta_diagonal]
  · exact le_of_lt (q.delta_pos i j h)

theorem pair_potential (i j : Fin n) :
    mass i * mass j * q.delta i j ^ 3 * squaredSeparation q.x q.y i j =
      mass i * mass j * q.delta i j := by
  by_cases h : i = j
  · subst j; simp [q.delta_diagonal]
  · calc
      _ = mass i * mass j * q.delta i j *
          (q.delta i j ^ 2 * squaredSeparation q.x q.y i j) := by ring
      _ = _ := by rw [q.distance i j h, mul_one]

theorem virial : q.doubledPotential = 2 * q.multiplier * q.inertia := by
  have hp : q.doubledPotential =
      ∑ i, ∑ j, mass i * mass j * q.delta i j ^ 3 * squaredSeparation q.x q.y i j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact (q.pair_potential i j).symm
  rw [hp]
  simp only [squaredSeparation, mul_add, Finset.sum_add_distrib]
  rw [coordinate_virial mass q.x q.delta q.delta_symm,
    coordinate_virial mass q.y q.delta q.delta_symm]
  simp_rw [← q.force_x, ← q.force_y]
  unfold inertia
  rw [← mul_add, ← Finset.sum_add_distrib]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem inertia_nonneg (hm : ∀ i, 0 < mass i) : 0 ≤ q.inertia :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hm i))
    (add_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem doubledPotential_pos (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j) :
    0 < q.doubledPotential := by
  have hp : ∀ i j, 0 ≤ mass i * mass j * q.delta i j :=
    fun i j => mul_nonneg (le_of_lt (mul_pos (hm i) (hm j))) (q.delta_nonneg i j)
  apply lt_of_lt_of_le (mul_pos (mul_pos (hm i) (hm j)) (q.delta_pos i j hij))
  apply le_trans (Finset.single_le_sum (fun k _ => hp i k) (Finset.mem_univ j))
  exact Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => hp k l))
    (Finset.mem_univ i)

theorem multiplier_pos (hm : ∀ i, 0 < mass i) (i j : Fin n) (hij : i ≠ j) :
    0 < q.multiplier := by
  have hp := q.doubledPotential_pos hm i j hij
  have hi := q.inertia_nonneg hm
  rw [q.virial] at hp
  by_contra h
  have hn := le_of_not_gt h
  have hz : 2 * q.multiplier * q.inertia ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hn) hi
  exact (not_lt_of_ge hz) hp

/-- Scale positions by s and inverse distances by 1/s. The cubic relation is
exactly what changes the force multiplier to one. -/
noncomputable def normalize (s : ℝ) (hs : s ≠ 0) (hs3 : s ^ 3 = q.multiplier) :
    NormalizedSystem ℝ n mass where
  x i := s * q.x i
  y i := s * q.y i
  delta i j := q.delta i j / s
  delta_symm i j := by rw [q.delta_symm i j]
  delta_diagonal i := by rw [q.delta_diagonal, zero_div]
  force_x i := by
    calc
      _ = s⁻¹ ^ 2 * (q.multiplier * q.x i) := by rw [← hs3]; field_simp
      _ = s⁻¹ ^ 2 * (∑ j, mass j * q.delta i j ^ 3 * (q.x i - q.x j)) := by
        rw [q.force_x]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        field_simp
  force_y i := by
    calc
      _ = s⁻¹ ^ 2 * (q.multiplier * q.y i) := by rw [← hs3]; field_simp
      _ = s⁻¹ ^ 2 * (∑ j, mass j * q.delta i j ^ 3 * (q.y i - q.y j)) := by
        rw [q.force_y]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        field_simp
  distance i j hij := by
    calc
      _ = q.delta i j ^ 2 * squaredSeparation q.x q.y i j := by
        unfold squaredSeparation
        field_simp
      _ = 1 := q.distance i j hij

theorem exists_positive_normalization (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ s : ℝ, 0 < s ∧ s ^ 3 = q.multiplier := by
  have hp := q.multiplier_pos hm i j hij
  refine ⟨q.multiplier ^ ((3 : ℝ)⁻¹), Real.rpow_pos_of_pos hp _, ?_⟩
  exact Real.rpow_inv_natCast_pow (le_of_lt hp) (by decide : (3 : ℕ) ≠ 0)

theorem exists_gauged_normalization (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j) :
    ∃ (s a b : ℝ) (p : NormalizedSystem ℝ n mass),
      0 < s ∧ s ^ 3 = q.multiplier ∧ a ^ 2 + b ^ 2 = 1 ∧
      p.InGauge i j ∧ 0 < p.x i - p.x j ∧
      (∀ k, p.x k = s * (a * q.x k + b * q.y k)) ∧
      (∀ k, p.y k = s * (-b * q.x k + a * q.y k)) ∧
      (∀ k l, p.delta k l = q.delta k l / s) ∧
      (∀ k l, k ≠ l → 0 < p.delta k l) := by
  obtain ⟨s, hs, hs3⟩ := q.exists_positive_normalization hm i j hij
  let p := q.normalize s (ne_of_gt hs) hs3
  obtain ⟨a, b, hab, hg, hx⟩ := p.exists_real_rotation_inGauge i j hij
  refine ⟨s, a, b, p.rotate a b hab, hs, hs3, hab, hg, hx, ?_, ?_, ?_, ?_⟩
  · intro k; change a * (s * q.x k) + b * (s * q.y k) = _; ring
  · intro k; change -b * (s * q.x k) + a * (s * q.y k) = _; ring
  · intro k l; rfl
  · intro k l hkl
    exact div_pos (q.delta_pos k l hkl) hs

end RealCentralSystem
end CentralConfigurations
