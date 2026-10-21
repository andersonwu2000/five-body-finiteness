import CentralConfigurations.Asymptotics.DisconnectedPairLimits
import CentralConfigurations.Asymptotics.SmallSeparationGeometry

/-!
# Shared-vertex torque in Chang, Section 10.6

The shared vertex's force equation expresses the crossed torque in products
of short coordinates and short-direction forces. These products are
O(scale squared), so the torque vanishes after cross-distance normalization.
The resulting four-term wedge relation retains all five bodies.
-/

namespace CentralConfigurations
open Filter Asymptotics
open scoped Topology BigOperators

def ScaledZWLimit.swapAtScale {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a) :
    ScaledZWLimit (fun t => (q t).swap) a where
  z := l.w
  w := l.z
  z_position := l.w_position
  w_position := l.z_position
  z_force := l.w_force
  w_force := l.z_force

theorem ScaledZWLimit.scale_bigO_delta {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (i j : Fin n) (hij : i ≠ j) : a =O[atTop] (fun t => (q t).delta i j) := by
  have hd (t : ℕ) : (q t).delta i j ≠ 0 := by
    intro hz
    have he := (q t).distance i j hij
    simp [hz] at he
  have he (t : ℕ) : (a t / (q t).delta i j)^2 =
      (a t * ((q t).z i - (q t).z j)) * (a t * ((q t).w i - (q t).w j)) := by
    field_simp [hd t]
    linear_combination -(a t)^2 * (q t).distance i j hij
  have ht := ((l.z_position i).sub (l.z_position j)).mul
    ((l.w_position i).sub (l.w_position j))
  have hpow : (fun t => (a t / (q t).delta i j)^2) =O[atTop] (fun _ => (1 : ℂ)^2) := by
    simpa only [he,mul_sub,one_pow] using ht.isBigO_one ℂ
  have hr := hpow.of_pow (by decide : (2 : ℕ) ≠ 0)
  exact (hr.mul (isBigO_refl (fun t => (q t).delta i j) atTop)).congr
    (fun t => div_mul_cancel₀ _ (hd t)) (fun t => one_mul _)

def fiveBodyCrossTorque {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) : ℂ :=
  mass 3 * mass 0 * q.torqueTerm 3 0 + mass 3 * mass 1 * q.torqueTerm 3 1 +
  mass 4 * mass 0 * q.torqueTerm 4 0 + mass 4 * mass 1 * q.torqueTerm 4 1

theorem five_body_cross_torque_identity {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) :
    fiveBodyCrossTorque q = mass 2 *
      (q.w 2 * q.z 2 - q.w 2 * (mass 0 * q.zForce 2 0 + mass 1 * q.zForce 2 1) -
       q.z 2 * (mass 3 * q.wForce 2 3 + mass 4 * q.wForce 2 4)) := by
  have ht := q.pair_torque_zero 3 4 (by decide)
  have hc : ({3,4} : Finset (Fin 5))ᶜ = {0,1,2} := by decide
  rw [hc] at ht
  simp only [Finset.sum_insert,Finset.sum_singleton,Finset.mem_insert,
    Finset.mem_singleton,Fin.isValue,Fin.reduceEq,or_self,not_false_eq_true] at ht
  have hz := q.force_z 2
  simp [Fin.sum_univ_succ] at hz
  calc
    fiveBodyCrossTorque q = -(mass 3 * mass 2 * q.torqueTerm 3 2 +
        mass 4 * mass 2 * q.torqueTerm 4 2) := by
      dsimp [fiveBodyCrossTorque]
      linear_combination ht
    _ = _ := by
      simp only [ZWSystem.torqueTerm,ZWSystem.zForce,ZWSystem.wForce,
        q.delta_symm 3 2,q.delta_symm 4 2]
      linear_combination -(mass 2)*q.w 2*hz

theorem five_body_cross_torque_bigO_square {mass : Fin 5 → ℂ}
    (q : ℕ → ZWSystem ℂ 5 mass) (a : ℕ → ℂ)
    (hz : (fun t => (q t).z 2) =O[atTop] a)
    (hw : (fun t => (q t).w 2) =O[atTop] a)
    (hz0 : (fun t => (q t).zForce 2 0) =O[atTop] a)
    (hz1 : (fun t => (q t).zForce 2 1) =O[atTop] a)
    (hw3 : (fun t => (q t).wForce 2 3) =O[atTop] a)
    (hw4 : (fun t => (q t).wForce 2 4) =O[atTop] a) :
    (fun t => fiveBodyCrossTorque (q t)) =O[atTop] (fun t => a t * a t) := by
  have h := (((hw.mul hz).sub
    (hw.mul ((hz0.const_mul_left (mass 0)).add (hz1.const_mul_left (mass 1))))).sub
    (hz.mul ((hw3.const_mul_left (mass 3)).add (hw4.const_mul_left (mass 4))))).const_mul_left (mass 2)
  exact h.congr_left (fun t => (five_body_cross_torque_identity (q t)).symm)

theorem ScaledZWLimit.five_body_cross_torque_normalized_zero {mass : Fin 5 → ℂ}
    {q : ℕ → ZWSystem ℂ 5 mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0))
    (h : (fun t => fiveBodyCrossTorque (q t)) =O[atTop] (fun t => a t * a t)) :
    Tendsto (fun t => fiveBodyCrossTorque (q t) / (q t).delta 3 0) atTop (𝓝 0) := by
  have hl : a =o[atTop] (fun _ => (1 : ℂ)) := (isLittleO_one_iff ℂ).mpr ha
  have hsq : (fun t => a t * a t) =o[atTop] a := by
    simpa only [one_mul] using hl.mul_isBigO (isBigO_refl a atTop)
  exact ((h.trans_isLittleO hsq).trans_isBigO (l.scale_bigO_delta 3 0 (by decide))).tendsto_div_nhds_zero

theorem five_body_cross_torque_root_relation {mass : Fin 5 → ℂ}
    (q : ℕ → ZWSystem ℂ 5 mass) (α β γ : ℂ)
    (hα : Tendsto (fun t => (q t).delta 3 1/(q t).delta 3 0) atTop (𝓝 α))
    (hβ : Tendsto (fun t => (q t).delta 4 0/(q t).delta 3 0) atTop (𝓝 β))
    (hγ : Tendsto (fun t => (q t).delta 4 1/(q t).delta 3 0) atTop (𝓝 γ))
    (h30 : Tendsto (fun t => (q t).torqueCorrection 3 0) atTop (𝓝 (-1)))
    (h31 : Tendsto (fun t => (q t).torqueCorrection 3 1) atTop (𝓝 (-1)))
    (h40 : Tendsto (fun t => (q t).torqueCorrection 4 0) atTop (𝓝 (-1)))
    (h41 : Tendsto (fun t => (q t).torqueCorrection 4 1) atTop (𝓝 (-1)))
    (hzero : Tendsto (fun t => fiveBodyCrossTorque (q t)/(q t).delta 3 0) atTop (𝓝 0)) :
    mass 3*mass 0 + mass 3*mass 1*α + mass 4*mass 0*β + mass 4*mass 1*γ = 0 := by
  let f : ℕ → ℂ := fun t => mass 3*mass 0*(q t).torqueCorrection 3 0 +
    mass 3*mass 1*((q t).delta 3 1/(q t).delta 3 0)*(q t).torqueCorrection 3 1 +
    mass 4*mass 0*((q t).delta 4 0/(q t).delta 3 0)*(q t).torqueCorrection 4 0 +
    mass 4*mass 1*((q t).delta 4 1/(q t).delta 3 0)*(q t).torqueCorrection 4 1
  have hf : f = (fun t => fiveBodyCrossTorque (q t)/(q t).delta 3 0) := by
    funext t
    have hd : (q t).delta 3 0 ≠ 0 := by
      intro hz
      have he := (q t).distance 3 0 (by decide)
      simp [hz] at he
    simp only [f,fiveBodyCrossTorque,ZWSystem.torqueTerm_eq]
    field_simp [hd]
  have hlim := (((h30.const_mul (mass 3*mass 0)).add
    ((hα.const_mul (mass 3*mass 1)).mul h31)).add
    ((hβ.const_mul (mass 4*mass 0)).mul h40)).add
    ((hγ.const_mul (mass 4*mass 1)).mul h41)
  change Tendsto f atTop (𝓝 _) at hlim
  have he := tendsto_nhds_unique hlim (hf.symm ▸ hzero)
  linear_combination -he

end CentralConfigurations
