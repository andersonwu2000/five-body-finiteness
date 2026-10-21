import Mathlib.Tactic

/-!
# The two one-variable equations for the kite mass relation

The variable is a ratio of actual limiting separations. The equations are
obtained by retaining both color triangle identities and the equal-position
balance. All divisions in the reduction have explicit nonzero hypotheses.
-/

namespace CentralConfigurations

def kiteSeparationEquation {R : Type*} [CommRing R] (a b c t : R) : R :=
  c ^ 2 * a ^ 2 * (t - 1) ^ 3 - c ^ 2 * b ^ 2 * t ^ 3 -
    a ^ 2 * b ^ 2 * t ^ 3 * (t - 1) ^ 3

def kiteBalanceEquation {R : Type*} [CommRing R] (a b c t : R) : R :=
  a ^ 3 * (t - 1) ^ 4 + b ^ 3 * t ^ 4 - c ^ 2 * (a + b)

theorem kite_equations_of_roots {K : Type*} [Field K] (a b c x y U V : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hU : U ≠ 0) (hV : V ≠ 0)
    (hx : x ^ 4 = (-b / c) * U) (hy : y ^ 4 = (a / c) * V)
    (hsz : x / U = 1 + y / V) (hsw : x / (-b / c) = 1 + y / (a / c))
    (hbalance : V - U = (a + b) / c) :
    ∃ t : K, kiteSeparationEquation a b c t = 0 ∧ kiteBalanceEquation a b c t = 0 := by
  let t := x / (-b / c)
  have hu : -b / c ≠ 0 := div_ne_zero (neg_ne_zero.mpr hb) hc
  have hv : a / c ≠ 0 := div_ne_zero ha hc
  have hxt : x = (-b / c) * t := by
    dsimp [t]
    field_simp [hb, hc]
  have hyt : y = (a / c) * (t - 1) := by
    have he : t - 1 = y / (a / c) := by
      change t = 1 + y / (a / c) at hsw
      linear_combination hsw
    rw [he]
    field_simp [ha, hc]
  have hUt : U = (-b / c) ^ 3 * t ^ 4 := by
    apply mul_left_cancel₀ hu
    calc
      (-b / c) * U = x ^ 4 := hx.symm
      _ = (-b / c) * ((-b / c) ^ 3 * t ^ 4) := by rw [hxt]; ring
  have hVt : V = (a / c) ^ 3 * (t - 1) ^ 4 := by
    apply mul_left_cancel₀ hv
    calc
      (a / c) * V = y ^ 4 := hy.symm
      _ = (a / c) * ((a / c) ^ 3 * (t - 1) ^ 4) := by rw [hyt]; ring
  have ht : t ≠ 0 := by
    intro he
    rw [he] at hUt
    simp only [zero_pow (by decide : 4 ≠ 0), mul_zero] at hUt
    exact hU hUt
  have ht1 : t - 1 ≠ 0 := by
    intro he
    rw [he] at hVt
    simp only [zero_pow (by decide : 4 ≠ 0), mul_zero] at hVt
    exact hV hVt
  have hzx : x / U = c ^ 2 / (b ^ 2 * t ^ 3) := by
    rw [hxt, hUt]
    field_simp [hb, hc, ht]
  have hzy : y / V = c ^ 2 / (a ^ 2 * (t - 1) ^ 3) := by
    rw [hyt, hVt]
    field_simp [ha, hc, ht1]
  have hF : kiteSeparationEquation a b c t = 0 := by
    rw [hzx, hzy] at hsz
    field_simp [ha, hb, ht, ht1] at hsz
    dsimp [kiteSeparationEquation]
    linear_combination hsz
  have hG : kiteBalanceEquation a b c t = 0 := by
    rw [hUt, hVt] at hbalance
    field_simp [hc] at hbalance
    dsimp [kiteBalanceEquation]
    linear_combination hbalance
  exact ⟨t, hF, hG⟩

end CentralConfigurations
