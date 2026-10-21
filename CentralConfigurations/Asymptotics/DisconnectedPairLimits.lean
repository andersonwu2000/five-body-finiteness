import CentralConfigurations.Asymptotics.TorqueLimits
import CentralConfigurations.Asymptotics.ThreeSquareLimits

/-!
# The cross-pair wedge limit in Chang, Section 9.4

All four terms are retained. Squared inverse-distance ratios and a common
compact extraction supply every possible complex root sign; no branch is chosen.
-/

namespace CentralConfigurations
open Filter
open scoped Topology BigOperators

namespace ScaledZWLimit
variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))

theorem delta_ratio_squared_limit
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (i j k r : Fin n) (hij : i ≠ j) (hkr : k ≠ r)
    (hz : l.z.position i ≠ l.z.position j)
    (hw : l.w.position i ≠ l.w.position j) :
    Tendsto (fun t => ((q t).delta i j / (q t).delta k r)^2) atTop
      (𝓝 (((l.z.position k-l.z.position r)/(l.z.position i-l.z.position j)) *
        ((l.w.position k-l.w.position r)/(l.w.position i-l.w.position j)))) := by
  have h := (l.z_separation_ratio_limit k r i j hkr hz).mul
    (l.w_separation_ratio_limit k r i j hkr hw)
  convert h using 1
  funext t
  have heq := (ZWSystem.pairEstimateData q hb i j hij).delta_ratio_square
    (ZWSystem.pairEstimateData q hb k r hkr) t
  change ((q t).delta i j / (q t).delta k r)^2 =
    (((q t).z k-(q t).z r)*((q t).w k-(q t).w r)) /
    (((q t).z i-(q t).z j)*((q t).w i-(q t).w j)) at heq
  rw [heq]
  simp only [div_eq_mul_inv, mul_inv]
  ring

theorem opposite_position_torque_limit (i j : Fin n) (hij : i ≠ j)
    (hzi : l.z.position i ≠ 0) (hzj : l.z.position j = 0)
    (hwi : l.w.position i = 0) (hwj : l.w.position j ≠ 0) :
    Tendsto (fun t => (q t).torqueCorrection i j) atTop (𝓝 (-1)) := by
  have hzd : l.z.position i ≠ l.z.position j := by rwa [hzj]
  have hwd : l.w.position i-l.w.position j ≠ 0 := by simpa [hwi] using hwj
  have hz := l.z_position_separation_ratio_limit i j hij hzd
  have hw : Tendsto (fun t => (q t).w i / ((q t).w i-(q t).w j)) atTop
      (𝓝 (l.w.position i/(l.w.position i-l.w.position j))) :=
    tendsto_ratio_of_scaled (inverseScale_ne_zero (q:=q) i j hij) hwd
    (l.w_position i) (by simpa only [mul_sub] using (l.w_position i).sub (l.w_position j))
  have h := hw.sub hz
  simpa only [← ZWSystem.torqueCorrection_eq _ i j hij, hwi, hzj,
    zero_div, sub_zero, div_self hzi, zero_sub] using h

end ScaledZWLimit

theorem four_body_cross_torque_zero {mass : Fin 4 → ℂ}
    (q : ZWSystem ℂ 4 mass) :
    mass 2*mass 0*q.torqueTerm 2 0 + mass 2*mass 1*q.torqueTerm 2 1 +
    mass 3*mass 0*q.torqueTerm 3 0 + mass 3*mass 1*q.torqueTerm 3 1 = 0 := by
  have h := q.pair_torque_zero 2 3 (by decide)
  have hs : ({2,3} : Finset (Fin 4))ᶜ = {0,1} := by decide
  rw [hs] at h
  simp only [Finset.sum_pair (by decide : (0 : Fin 4) ≠ 1)] at h
  linear_combination h

theorem four_body_cross_torque_root_relation {mass : Fin 4 → ℂ}
    (q : ℕ → ZWSystem ℂ 4 mass) (α β γ : ℂ)
    (hα : Tendsto (fun t => (q t).delta 2 1/(q t).delta 2 0) atTop (𝓝 α))
    (hβ : Tendsto (fun t => (q t).delta 3 0/(q t).delta 2 0) atTop (𝓝 β))
    (hγ : Tendsto (fun t => (q t).delta 3 1/(q t).delta 2 0) atTop (𝓝 γ))
    (h20 : Tendsto (fun t => (q t).torqueCorrection 2 0) atTop (𝓝 (-1)))
    (h21 : Tendsto (fun t => (q t).torqueCorrection 2 1) atTop (𝓝 (-1)))
    (h30 : Tendsto (fun t => (q t).torqueCorrection 3 0) atTop (𝓝 (-1)))
    (h31 : Tendsto (fun t => (q t).torqueCorrection 3 1) atTop (𝓝 (-1))) :
    mass 2*mass 0 + mass 2*mass 1*α + mass 3*mass 0*β + mass 3*mass 1*γ = 0 := by
  let f : ℕ → ℂ := fun t => mass 2*mass 0*(q t).torqueCorrection 2 0 +
    mass 2*mass 1*((q t).delta 2 1/(q t).delta 2 0)*(q t).torqueCorrection 2 1 +
    mass 3*mass 0*((q t).delta 3 0/(q t).delta 2 0)*(q t).torqueCorrection 3 0 +
    mass 3*mass 1*((q t).delta 3 1/(q t).delta 2 0)*(q t).torqueCorrection 3 1
  have hzero (t : ℕ) : f t = 0 := by
    have hd : (q t).delta 2 0 ≠ 0 := by
      intro hz
      have heq := (q t).distance 2 0 (by decide)
      simp [hz] at heq
    have ht := four_body_cross_torque_zero (q t)
    simp only [ZWSystem.torqueTerm_eq] at ht
    dsimp [f]
    field_simp [hd]
    linear_combination ht
  have hlim := (((h20.const_mul (mass 2*mass 0)).add
    ((hα.const_mul (mass 2*mass 1)).mul h21)).add
    ((hβ.const_mul (mass 3*mass 0)).mul h30)).add
    ((hγ.const_mul (mass 3*mass 1)).mul h31)
  change Tendsto f atTop (𝓝 _) at hlim
  have heq := tendsto_nhds_unique hlim
    (show Tendsto f atTop (𝓝 0) from by
      have hf : f = (fun _ => 0) := funext hzero
      rw [hf]
      exact tendsto_const_nhds)
  linear_combination -heq

end CentralConfigurations
