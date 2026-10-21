import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

namespace CentralConfigurations.FiveBody.D9

noncomputable def cubeRoot (x : ℝ) : ℝ := x ^ (1 / 3 : ℝ)

theorem cubeRoot_pos {x : ℝ} (hx : 0 < x) : 0 < cubeRoot x :=
  Real.rpow_pos_of_pos hx _

theorem cubeRoot_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ cubeRoot x :=
  Real.rpow_nonneg hx _

theorem cubeRoot_cube {x : ℝ} (hx : 0 ≤ x) : cubeRoot x ^ 3 = x := by
  simpa [cubeRoot, one_div] using Real.rpow_inv_natCast_pow hx (by decide : (3 : ℕ) ≠ 0)

theorem cube_mono {x y : ℝ} (h : x ^ 3 ≤ y ^ 3) : x ≤ y := by
  exact (Odd.strictMono_pow (by decide : Odd 3)).le_iff_le.mp h

theorem cube_strict {x y : ℝ} (h : x ^ 3 < y ^ 3) : x < y := by
  exact (Odd.strictMono_pow (by decide : Odd 3)).lt_iff_lt.mp h

theorem cube_inj {x y : ℝ} (h : x ^ 3 = y ^ 3) : x = y := by
  exact (Odd.strictMono_pow (by decide : Odd 3)).injective h

theorem cubeRoot_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cubeRoot (x*y) = cubeRoot x * cubeRoot y := by
  apply cube_inj
  rw [mul_pow, cubeRoot_cube (mul_nonneg hx hy), cubeRoot_cube hx, cubeRoot_cube hy]

theorem cubeRoot_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    cubeRoot (x/y) = cubeRoot x / cubeRoot y := by
  apply cube_inj
  rw [div_pow, cubeRoot_cube (div_nonneg hx hy), cubeRoot_cube hx, cubeRoot_cube hy]

theorem scaled_attachment_root {M K a : ℝ} (hM : 0 < M) (hK : 0 ≤ K) (ha : 0 < a) :
    cubeRoot M * a * cubeRoot (K/(M*a)) = cubeRoot K * cubeRoot a^2 := by
  apply cube_inj
  simp only [mul_pow]
  rw [show (cubeRoot a^2)^3 = (cubeRoot a^3)^2 by ring,
    cubeRoot_cube hM.le, cubeRoot_cube (div_nonneg hK (mul_pos hM ha).le),
    cubeRoot_cube hK, cubeRoot_cube ha.le]
  field_simp [ne_of_gt hM, ne_of_gt ha]
  <;> ring

theorem scaled_outer_root {M P : ℝ} (hM : 0 ≤ M) (hP : 0 < P) :
    cubeRoot M * cubeRoot (1/P) = cubeRoot (M/P) := by
  rw [← cubeRoot_mul hM (by positivity)]
  congr 1
  ring

theorem two_term_holder_cube (p q x y : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (p*x^2+q*y^2)^3 ≤ (p^3+q^3)*(x^3+y^3)^2 := by
  have h : 0 ≤ (p*y-q*x)^2 * (2*p*x^3*y+p*y^4+q*x^4+2*q*x*y^3) :=
    mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith only [h]

theorem pair_cube_gap {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    p^3 + q^3 < (p+q-p*q/(p+q))^3 := by
  have hP : 0 < p+q := by positivity
  have hrem : 0 < (p*q)^2*(3*(p+q)^2-p*q)/(p+q)^3 := by
    apply div_pos
    · apply mul_pos (sq_pos_of_pos (by positivity))
      nlinarith [sq_nonneg (p-q)]
    · positivity
  have hid : (p+q-p*q/(p+q))^3-(p^3+q^3) =
      (p*q)^2*(3*(p+q)^2-p*q)/(p+q)^3 := by
    field_simp
    <;> ring
  linarith

theorem exterior_cube_gap {K P : ℝ} (hK : 0 < K) (hP : 0 < P) :
    cubeRoot ((K+P)/P) < 1 + K/(3*P) := by
  apply cube_strict
  rw [cubeRoot_cube (by positivity)]
  have hrem : 0 < K^2/(3*P^2)+K^3/(27*P^3) := by positivity
  have hid : (1+K/(3*P))^3-(K+P)/P = K^2/(3*P^2)+K^3/(27*P^3) := by
    field_simp
    <;> ring
  linarith

/-- The phase-uniform envelope after multiplication by the positive cube
root of total mass.  Positive mass at the unused triangle vertex is retained. -/
theorem scaled_envelope_lt {a b c p q : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hp : 0 < p) (hq : 0 < q) :
    cubeRoot (a+b+c) * (p*cubeRoot a^2+q*cubeRoot b^2) +
      p*q*cubeRoot ((a+b+c+p+q)/(p+q)) <
      (a*b+a*c+b*c)+(a+b+c)*(p+q)+p*q := by
  let K := a+b+c
  let P := p+q
  have hK : 0 < K := by dsimp [K]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hR : 0 < P-p*q/P := by
    have : p*q < P^2 := by dsimp [P]; nlinarith [sq_nonneg (p-q)]
    have hd : p*q/P < P := (div_lt_iff₀ hP).2 (by nlinarith)
    linarith
  have hh := two_term_holder_cube p q (cubeRoot a) (cubeRoot b)
    hp.le hq.le (cubeRoot_nonneg ha.le) (cubeRoot_nonneg hb.le)
  rw [cubeRoot_cube ha.le, cubeRoot_cube hb.le] at hh
  have hab : (a+b)^2 ≤ K^2 := by dsimp [K]; nlinarith
  have hcoeff : 0 < p^3+q^3 := by positivity
  have hh' : (p*cubeRoot a^2+q*cubeRoot b^2)^3 ≤ (p^3+q^3)*K^2 :=
    hh.trans (mul_le_mul_of_nonneg_left hab hcoeff.le)
  have hpair : p^3+q^3 < (P-p*q/P)^3 := pair_cube_gap hp hq
  have hat : cubeRoot K*(p*cubeRoot a^2+q*cubeRoot b^2) < K*(P-p*q/P) := by
    apply cube_strict
    rw [mul_pow, cubeRoot_cube hK.le, mul_pow]
    have h1 := mul_le_mul_of_nonneg_left hh' hK.le
    have h2 := mul_lt_mul_of_pos_left hpair (pow_pos hK 3)
    nlinarith only [h1, h2]
  have hout := exterior_cube_gap hK hP
  have hout' := mul_lt_mul_of_pos_left hout (mul_pos hp hq)
  have hid : K*(P-p*q/P)+p*q*(1+K/(3*P)) =
      K*P+p*q-2*K*p*q/(3*P) := by ring
  have hgap : 0 < (a*b+a*c+b*c)+2*K*p*q/(3*P) := by positivity
  have hsum := add_lt_add hat hout'
  rw [hid] at hsum
  have hfinal : cubeRoot K * (p*cubeRoot a^2+q*cubeRoot b^2) +
      p*q*cubeRoot ((K+P)/P) < (a*b+a*c+b*c)+K*P+p*q := by linarith
  simpa only [K, P, add_assoc] using hfinal

end CentralConfigurations.FiveBody.D9
