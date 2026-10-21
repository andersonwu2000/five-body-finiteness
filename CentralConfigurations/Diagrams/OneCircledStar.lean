import CentralConfigurations.Diagrams.DoubleTriangles

/-!
# The stronger one-circle test in Appendix I

The Mathematica `RuleTriangle2Q` (printed p. 109) forbids a circled vertex
joined to two distinct uncircled vertices. This is stronger than the numerical
product inequality printed in Theorem 3.4(b): that inequality does not exclude
a complete triangle with exactly one circle. The appendix restriction follows
from the already proved maximal-stroke triangle theorem, including its
conclusion that the remaining separation is maximal.
-/

namespace CentralConfigurations

def OneCircledStarRule {n : ℕ} (A : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
    A i i = 1 → A j j = 0 → A k k = 0 → A i j * A i k = 0

instance oneCircledStarRule_decidable {n : ℕ} (A : Fin n → Fin n → ℕ) :
    Decidable (OneCircledStarRule A) := by
  unfold OneCircledStarRule
  infer_instance

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

/-- Both neighbors would have leading position zero, whereas two successive
maximal strokes force their leading positions to be different. -/
theorem no_one_circled_star (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hi : l.z.position i ≠ 0) (hj : l.z.position j = 0) (hk : l.z.position k = 0)
    (hijz : l.z.force i j ≠ 0) (hikz : l.z.force i k ≠ 0) : False := by
  have hji : l.z.force j i ≠ 0 := by
    rw [l.z.antisymm j i]
    exact neg_ne_zero.mpr hijz
  have hji' : l.z.position j ≠ l.z.position i := by
    simpa only [hj, ne_eq, eq_comm] using hi
  have hik' : l.z.position i ≠ l.z.position k := by
    simpa only [hk] using hi
  have h := l.maximal_z_triangle hb j i k hij.symm hik hjk hji hji' hikz hik'
  exact h.2 (hj.trans hk.symm)

theorem one_circled_star_rule : OneCircledStarRule l.z.matrix := by
  intro i j k hij hik hjk hi hj hk
  by_contra h
  have he₁ : l.z.matrix i j = 1 :=
    (l.z.matrix_binary i j).resolve_left (fun hzero => h (by simp [hzero]))
  have he₂ : l.z.matrix i k = 1 :=
    (l.z.matrix_binary i k).resolve_left (fun hzero => h (by simp [hzero]))
  apply l.no_one_circled_star hb i j k hij hik hjk
  · simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hi
  · simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hj
  · simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hk
  · simpa [OneColorLimit.matrix, OneColorLimit.Incident, hij] using he₁
  · simpa [OneColorLimit.matrix, OneColorLimit.Incident, hik] using he₂

theorem one_circled_star_rules :
    OneCircledStarRule l.z.matrix ∧ OneCircledStarRule l.w.matrix :=
  ⟨l.one_circled_star_rule hb,
    (l.swapBalanced hb).one_circled_star_rule (fun t => (hb t).symm)⟩

end ScaledZWLimit
end CentralConfigurations
