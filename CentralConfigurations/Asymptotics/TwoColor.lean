import CentralConfigurations.Asymptotics.Extraction

/-!
# Two-color limits and the circling method

Scaled positions and forces converge with a common scale for both colors.
The circling method of Chang's Theorem 2.6 follows from the polynomial
force-distance identity as that scale tends to zero. Balancing.lean
constructs the common-scale limits from balanced singular sequences.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

structure ScaledZWLimit {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (a : ℕ → ℂ) where
  z : OneColorLimit ℂ n mass
  w : OneColorLimit ℂ n mass
  z_position : ∀ i, Tendsto (fun t => a t * (q t).z i) atTop (𝓝 (z.position i))
  w_position : ∀ i, Tendsto (fun t => a t * (q t).w i) atTop (𝓝 (w.position i))
  z_force : ∀ i j, Tendsto (fun t => a t * (q t).zForce i j) atTop (𝓝 (z.force i j))
  w_force : ∀ i j, Tendsto (fun t => a t * (q t).wForce i j) atTop (𝓝 (w.force i j))

def ScaledZWLimit.swap {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a) :
    ScaledZWLimit (fun t => (q t).swap) a where
  z := l.w
  w := l.z
  z_position := l.w_position
  w_position := l.z_position
  z_force := l.w_force
  w_force := l.z_force

/-- A w-stroke forces equality of the leading z-positions. -/
theorem ScaledZWLimit.w_stroke_z_close {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (i j : Fin n) (hij : i ≠ j)
    (hw : l.w.force i j ≠ 0) : l.z.position i = l.z.position j := by
  have hleft := ((l.w_force i j).pow 3).mul
    (((l.z_position i).sub (l.z_position j)).pow 4)
  have hright := (ha.pow 6).mul (l.z_force i j)
  have heq : (fun t => (a t * (q t).wForce i j) ^ 3 *
        (a t * (q t).z i - a t * (q t).z j) ^ 4) =
      (fun t => (a t) ^ 6 * (a t * (q t).zForce i j)) :=
    funext fun t => (q t).scaled_force_identity (a t) i j hij
  rw [heq] at hleft
  have h := tendsto_nhds_unique hleft hright
  simp only [zero_pow (by decide : (6 : ℕ) ≠ 0), zero_mul] at h
  have hd := (mul_eq_zero.mp h).resolve_left (pow_ne_zero 3 hw)
  by_contra hn
  exact pow_ne_zero 4 (sub_ne_zero.mpr hn) hd

theorem ScaledZWLimit.z_stroke_w_close {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (i j : Fin n) (hij : i ≠ j)
    (hz : l.z.force i j ≠ 0) : l.w.position i = l.w.position j :=
  l.swap.w_stroke_z_close ha i j hij hz

theorem ScaledZWLimit.w_stroke_circle_iff {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (i j : Fin n) (hij : i ≠ j)
    (hw : l.w.force i j ≠ 0) : l.z.position i ≠ 0 ↔ l.z.position j ≠ 0 := by
  rw [l.w_stroke_z_close ha i j hij hw]

end CentralConfigurations
