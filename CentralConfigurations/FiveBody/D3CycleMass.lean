import CentralConfigurations.FiveBody.PhysicalPotentialFloor
import Mathlib.Tactic

namespace CentralConfigurations.FiveBody.D3

/-- Cube-root concavity in its polynomial form; no root sign is chosen. -/
theorem side_gap (k K w P v x : ℝ) (hw : 0<w) (hP : 0<P)
    (hv : v≠0) (hk : k^3=K) (hx : v*x^3=1)
    (hm : w*K=v*(w+P)) : k*w*x < w+P/3 := by
  have he : (k*w*x)^3=w^2*(w+P) := by
    apply (mul_left_cancel₀ hv)
    linear_combination v*w^3*x^3*hk + v*w^2*(w+P)*hx + w^2*v*x^3*hm
  have hh : 0<w*P^2/3+P^3/27 := by positivity
  have hd : (w+P/3)^3-(k*w*x)^3=w*P^2/3+P^3/27 := by rw [he]; ring
  exact (Odd.strictMono_pow (by decide : Odd 3)).lt_iff_lt.mp (by linarith)

def coreMass (m : Fin 5 → ℝ) := m 1+m 2+m 3+m 4
def corePairs (m : Fin 5 → ℝ) :=
  m 1*m 2+m 1*m 3+m 1*m 4+m 2*m 3+m 2*m 4+m 3*m 4
def cycleValue (m : Fin 5 → ℝ) (x : Fin 4 → ℝ) :=
  m 1*m 2*x 0+m 2*m 3*x 1+m 3*m 4*x 2+m 1*m 4*x 3

theorem core_gap {m : Fin 5 → ℝ} (hm : ∀ i, 0<m i)
    (hopp : m 1*m 3=m 2*m 4) (x : Fin 4 → ℝ)
    (hx0 : (m 1+m 2)*(x 0)^3=1) (hx1 : (m 2+m 3)*(x 1)^3=1)
    (hx2 : (m 3+m 4)*(x 2)^3=1) (hx3 : (m 1+m 4)*(x 3)^3=1)
    {k : ℝ} (hk : k^3=coreMass m) :
    k*cycleValue m x < corePairs m := by
  have hp1 := hm 1; have hp2 := hm 2; have hp3 := hm 3; have hp4 := hm 4
  have hP : 0<m 1*m 3 := mul_pos hp1 hp3
  have h0 := side_gap k (coreMass m) (m 1*m 2) (m 1*m 3) (m 1+m 2) (x 0)
    (by positivity) hP (by positivity) hk hx0 (by dsimp [coreMass]; linear_combination -(m 1)*hopp)
  have h1 := side_gap k (coreMass m) (m 2*m 3) (m 1*m 3) (m 2+m 3) (x 1)
    (by positivity) hP (by positivity) hk hx1 (by dsimp [coreMass]; linear_combination -(m 3)*hopp)
  have h2 := side_gap k (coreMass m) (m 3*m 4) (m 1*m 3) (m 3+m 4) (x 2)
    (by positivity) hP (by positivity) hk hx2 (by dsimp [coreMass]; linear_combination -(m 3)*hopp)
  have h3 := side_gap k (coreMass m) (m 1*m 4) (m 1*m 3) (m 1+m 4) (x 3)
    (by positivity) hP (by positivity) hk hx3 (by dsimp [coreMass]; linear_combination -(m 1)*hopp)
  dsimp [cycleValue,corePairs]
  nlinarith

theorem fifth_mass_gap {m : Fin 5 → ℝ} (hm : ∀ i, 0<m i) :
    totalMass m*(corePairs m)^3 < coreMass m*(pairMassSum m)^3 := by
  have hp0 := hm 0; have hp1 := hm 1; have hp2 := hm 2; have hp3 := hm 3; have hp4 := hm 4
  have hK : 0<coreMass m := by dsimp [coreMass]; positivity
  have hJ : 0<corePairs m := by dsimp [corePairs]; positivity
  have hB : 0<3*(coreMass m)^2-corePairs m := by
    dsimp [coreMass,corePairs]
    nlinarith [sq_nonneg (m 1),sq_nonneg (m 2),sq_nonneg (m 3),sq_nonneg (m 4),
      mul_pos hp1 hp2,mul_pos hp1 hp3,mul_pos hp1 hp4,mul_pos hp2 hp3,
      mul_pos hp2 hp4,mul_pos hp3 hp4]
  have hS : pairMassSum m=corePairs m+m 0*coreMass m := by
    simp [pairMassSum,corePairs,coreMass,Fin.sum_univ_succ]; ring
  have hM : totalMass m=coreMass m+m 0 := by simp [totalMass,coreMass,Fin.sum_univ_succ]; ring
  rw [hS,hM]
  have hid : coreMass m*(corePairs m+m 0*coreMass m)^3-(coreMass m+m 0)*(corePairs m)^3 =
      m 0*((corePairs m)^2*(3*(coreMass m)^2-corePairs m)+
        3*(m 0)*(corePairs m)*(coreMass m)^3+(m 0)^2*(coreMass m)^4) := by ring
  have hp : 0<m 0*((corePairs m)^2*(3*(coreMass m)^2-corePairs m)+
        3*(m 0)*(corePairs m)*(coreMass m)^3+(m 0)^2*(coreMass m)^4) := by positivity
  linarith

theorem energy_gap {m : Fin 5 → ℝ} {I0 : ℝ} (hm : ∀ i, 0<m i)
    (hopp : m 1*m 3=m 2*m 4) (hphysical : PhysicalPotentialLevel m I0)
    (x : Fin 4 → ℝ) (hx0 : (m 1+m 2)*(x 0)^3=1) (hx1 : (m 2+m 3)*(x 1)^3=1)
    (hx2 : (m 3+m 4)*(x 2)^3=1) (hx3 : (m 1+m 4)*(x 3)^3=1)
    (hI : I0 ≤ cycleValue m x) : False := by
  have hK : 0<coreMass m := by
    have := hm 1; have := hm 2; have := hm 3; have := hm 4
    dsimp [coreMass]; positivity
  let k := (coreMass m)^((3:ℝ)⁻¹)
  have hk : k^3=coreMass m := Real.rpow_inv_natCast_pow (le_of_lt hK) (by decide)
  have hkpos : 0<k := Real.rpow_pos_of_pos hK _
  have hcore := core_gap hm hopp x hx0 hx1 hx2 hx3 hk
  have hki : k*I0 < corePairs m := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hI (le_of_lt hkpos)) hcore
  have hc := (Odd.strictMono_pow (by decide : Odd 3)) hki
  change (k*I0)^3 < (corePairs m)^3 at hc
  rw [mul_pow,hk] at hc
  have hM : 0<totalMass m := by
    unfold totalMass
    exact Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty
  have hf := mul_le_mul_of_nonneg_left hphysical.2 (le_of_lt hK)
  have hg := fifth_mass_gap hm
  have hh := mul_lt_mul_of_pos_left hc hM
  nlinarith

end CentralConfigurations.FiveBody.D3
