import CentralConfigurations.Model.Invariance
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The real rotational gauge in Section 2.1

An orthogonal rotation preserves every normalized equation and every inverse
distance. For a prescribed distinct pair, an explicit rotation makes the two
y-coordinates equal and puts their x-separation on the positive real axis.
-/

namespace CentralConfigurations

open scoped BigOperators

theorem squaredSeparation_rotate {K : Type*} [CommRing K] {n : ℕ}
    (x y : Fin n → K) (a b : K) (hab : a ^ 2 + b ^ 2 = 1) (i j : Fin n) :
    squaredSeparation (fun k => a * x k + b * y k)
      (fun k => -b * x k + a * y k) i j = squaredSeparation x y i j := by
  unfold squaredSeparation
  calc
    _ = (a ^ 2 + b ^ 2) * ((x i - x j) ^ 2 + (y i - y j) ^ 2) := by ring
    _ = _ := by rw [hab, one_mul]

def NormalizedSystem.rotate {K : Type*} [CommRing K] {n : ℕ} {mass : Fin n → K}
    (q : NormalizedSystem K n mass) (a b : K) (hab : a ^ 2 + b ^ 2 = 1) :
    NormalizedSystem K n mass where
  x k := a * q.x k + b * q.y k
  y k := -b * q.x k + a * q.y k
  delta := q.delta
  delta_symm := q.delta_symm
  delta_diagonal := q.delta_diagonal
  force_x i := by
    calc
      _ = a * (∑ j, mass j * q.delta i j ^ 3 * (q.x i - q.x j)) +
          b * (∑ j, mass j * q.delta i j ^ 3 * (q.y i - q.y j)) := by
            rw [← q.force_x i, ← q.force_y i]
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  force_y i := by
    calc
      _ = -b * (∑ j, mass j * q.delta i j ^ 3 * (q.x i - q.x j)) +
          a * (∑ j, mass j * q.delta i j ^ 3 * (q.y i - q.y j)) := by
            rw [← q.force_x i, ← q.force_y i]
      _ = _ := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  distance i j hij := by
    rw [squaredSeparation_rotate _ _ _ _ hab]
    exact q.distance i j hij

theorem NormalizedSystem.real_separation_pos {n : ℕ} {mass : Fin n → ℝ}
    (q : NormalizedSystem ℝ n mass) {i j : Fin n} (hij : i ≠ j) :
    0 < squaredSeparation q.x q.y i j := by
  have hn := q.separation_ne_zero hij
  have hp : 0 ≤ squaredSeparation q.x q.y i j :=
    add_nonneg (sq_nonneg _) (sq_nonneg _)
  exact lt_of_le_of_ne hp (Ne.symm hn)

theorem NormalizedSystem.exists_real_rotation_inGauge {n : ℕ} {mass : Fin n → ℝ}
    (q : NormalizedSystem ℝ n mass) (i j : Fin n) (hij : i ≠ j) :
    ∃ (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1),
      (q.rotate a b hab).InGauge i j ∧
      0 < (q.rotate a b hab).x i - (q.rotate a b hab).x j := by
  let dx := q.x i - q.x j
  let dy := q.y i - q.y j
  let r := Real.sqrt (dx ^ 2 + dy ^ 2)
  have hsum : 0 < dx ^ 2 + dy ^ 2 := q.real_separation_pos hij
  have hr : 0 < r := Real.sqrt_pos.mpr hsum
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hr2 : r ^ 2 = dx ^ 2 + dy ^ 2 := Real.sq_sqrt (le_of_lt hsum)
  have hab : (dx / r) ^ 2 + (dy / r) ^ 2 = 1 := by
    field_simp
    nlinarith [hr2]
  refine ⟨dx / r, dy / r, hab, ⟨hij, ?_⟩, ?_⟩
  · change -(dy / r) * q.x i + (dx / r) * q.y i =
      -(dy / r) * q.x j + (dx / r) * q.y j
    dsimp only [dx, dy]
    ring
  · have he : (q.rotate (dx / r) (dy / r) hab).x i -
        (q.rotate (dx / r) (dy / r) hab).x j = r := by
      change (dx / r * q.x i + dy / r * q.y i) -
        (dx / r * q.x j + dy / r * q.y j) = r
      field_simp
      dsimp only [dx, dy] at hr2
      nlinarith [hr2]
    rw [he]
    exact hr

theorem NormalizedSystem.map_inGauge {K L : Type*} [CommRing K] [CommRing L]
    {n : ℕ} {mass : Fin n → K} (q : NormalizedSystem K n mass)
    (f : K →+* L) {i j : Fin n} (h : q.InGauge i j) : (q.map f).InGauge i j :=
  ⟨h.1, congrArg f h.2⟩

end CentralConfigurations
