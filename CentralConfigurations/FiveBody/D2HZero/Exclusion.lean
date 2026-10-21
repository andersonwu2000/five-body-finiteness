import CentralConfigurations.FiveBody.D2HZero.NormalizedForces
import CentralConfigurations.FiveBody.D2Exceptional.HZeroClassification
import CentralConfigurations.FiveBody.D2EllZero.Extraction

namespace CentralConfigurations.FiveBody.D2.HZero
open Exceptional
open scoped BigOperators
set_option maxHeartbeats 4000000

theorem bilinear_inertia_zero_of_centered_response_zero {m : Fin 5 → ℝ}
    (s : FiveBodySource18Certificate m) (signed : SignedEulerMetric s.triangle)
    (hm : ∀ i, 0 < m i) (hzero : ∀ i, centeredCrossResponse s i=0) :
    (∑ i : Fin 3, (m (i.castLE (by decide)) : ℂ)*s.triangle.w i^2)=0 := by
  obtain ⟨c⟩ := exists_circleChart s hm hzero
  obtain ⟨rows⟩ := exists_originalRows c signed
  have hm2 : (c.mass 2 : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (hm ((c.order 2).castLE (by decide)))
  have hP := quintic_of_original_rows hm2 c.omega_ne_one c.y_ne_one c.y_ne_omega
    rows.center rows.row0 rows.row1
  change eulerQuintic ((c.h-1)/2) c.y rows.sign13 rows.sign23=0 at hP
  obtain ⟨_,_,hy⟩ := normalized_circle_classification c.h_square c.third_norm
    rows.sign13_values rows.sign23_values hP
  change c.y= -(c.h+1)/2 at hy
  have hc := rows.center
  change (c.mass 0 : ℂ)+(c.mass 1 : ℂ)*((c.h-1)/2)+(c.mass 2 : ℂ)*c.y=0 at hc
  rw [hy] at hc
  obtain ⟨ha,hb⟩ := surviving_center_equal_masses c.h_square hc
  have hnorm : (∑ i : Fin 3, (c.mass i : ℂ)*(![1,c.omega,c.y] i)^2)=0 := by
    simp [Fin.sum_univ_succ]
    rw [ha,hb,hy]
    dsimp [CircleChart.omega]
    linear_combination surviving_inertia_zero (c.mass 2 : ℂ) c.h_square
  calc
    _ = ∑ i : Fin 3, (m ((c.order i).castLE (by decide)) : ℂ)*s.triangle.w (c.order i)^2 :=
      (Equiv.sum_comp c.order (fun i => (m (i.castLE (by decide)) : ℂ)*s.triangle.w i^2)).symm
    _ = c.gamma^2*(∑ i : Fin 3, (c.mass i : ℂ)*(![1,c.omega,c.y] i)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [c.positions i]
      dsimp [CircleChart.mass]
      ring
    _ = 0 := by rw [hnorm,mul_zero]

theorem PhysicalEulerLimit.not_centered_response_zero {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
    (s : PhysicalEulerLimit m q l I0) (hm : ∀ i, 0 < m i) :
    ¬ (∀ i, centeredCrossResponse s.toFiveBodySource18Certificate i=0) := by
  intro hzero
  exact s.nonisotropic (bilinear_inertia_zero_of_centered_response_zero
    s.toFiveBodySource18Certificate s.signedEuler hm hzero)

theorem PhysicalEulerLimit.exists_centered_response_ne_zero {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
    (s : PhysicalEulerLimit m q l I0) (hm : ∀ i, 0 < m i) :
    ∃ i, centeredCrossResponse s.toFiveBodySource18Certificate i ≠ 0 := by
  exact not_forall.mp (PhysicalEulerLimit.not_centered_response_zero s hm)

end CentralConfigurations.FiveBody.D2.HZero
