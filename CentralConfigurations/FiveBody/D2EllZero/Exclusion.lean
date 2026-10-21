import CentralConfigurations.FiveBody.D2EllZero.OrderedTorque
import CentralConfigurations.FiveBody.D2EllZero.CenteredNorms
import CentralConfigurations.FiveBody.D2EllZero.RoleOrders

namespace CentralConfigurations.FiveBody.D2.EllZero
open Exceptional
open scoped BigOperators
set_option maxHeartbeats 3000000

theorem false_of_certificate_ell_zero {m : Fin 5 → ℝ}
    (s : FiveBodySource18Certificate m) (signed : SignedEulerMetric s.triangle)
    (hm : ∀ i, 0 < m i) (hell : transverseEigenvalue s.triangle=0) : False := by
  obtain ⟨d,hcases⟩ := actual_ell_zero_mass_cases signed
    (fun i => hm (i.castLE (by decide))) hell
  rcases hcases with ⟨_,_,hk,ha,hb⟩ | ⟨_,_,hk,ha,hb⟩ | ⟨_,_,hk,ha,hb⟩
  · change m 0=m 2 at ha
    change m 1=5*m 0 at hb
    have hc := s.triangle.mass_center_w
    simp [Fin.sum_univ_succ] at hc
    rw [← ha,hb] at hc
    push_cast at hc
    have hmC : (m 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hm 0)
    have hc0 : s.triangle.w 0+5*s.triangle.w 1+s.triangle.w 2=0 := by
      apply mul_left_cancel₀ hmC
      linear_combination hc
    obtain ⟨hout,hheavy⟩ := centered0 hk d.difference01 d.difference02 hc0
    let e : Fin 3 ≃ Fin 3 := role0
    let w : Fin 3 → ℂ := fun i => s.triangle.w (e i)
    let u : Fin 3 → ℂ := fun i => s.cross 0 (e i)
    let v : Fin 3 → ℂ := fun i => s.cross 1 (e i)
    have ht := s.cross_torque
    simp [Fin.sum_univ_succ] at ht
    rw [← ha,hb] at ht
    push_cast at ht
    apply false_of_ordered_pair_triangle_torque (hm 3) (hm 4) (hm 0)
      (s.pairZ_ne_zero 0) (fun i => s.w_ne_zero (e i)) s.pair_balance
      (fun i => s.cross_square 0 (e i)) (fun i => s.cross_square 1 (e i))
      (w := w) (u := u) (v := v)
    · simpa [w,e,role0] using hout
    · simpa [w,e,role0] using hheavy
    · dsimp [u,v,e,role0]
      linear_combination ht
  · change m 0=m 1 at ha
    change m 2=5*m 0 at hb
    have hc := s.triangle.mass_center_w
    simp [Fin.sum_univ_succ] at hc
    rw [← ha,hb] at hc
    push_cast at hc
    have hmC : (m 0 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hm 0)
    have hc0 : s.triangle.w 0+s.triangle.w 1+5*s.triangle.w 2=0 := by
      apply mul_left_cancel₀ hmC
      linear_combination hc
    obtain ⟨hout,hheavy⟩ := centered1 hk d.difference01 d.difference02 hc0
    let e : Fin 3 ≃ Fin 3 := role1
    let w : Fin 3 → ℂ := fun i => s.triangle.w (e i)
    let u : Fin 3 → ℂ := fun i => s.cross 0 (e i)
    let v : Fin 3 → ℂ := fun i => s.cross 1 (e i)
    have ht := s.cross_torque
    simp [Fin.sum_univ_succ] at ht
    rw [← ha,hb] at ht
    push_cast at ht
    apply false_of_ordered_pair_triangle_torque (hm 3) (hm 4) (hm 0)
      (s.pairZ_ne_zero 0) (fun i => s.w_ne_zero (e i)) s.pair_balance
      (fun i => s.cross_square 0 (e i)) (fun i => s.cross_square 1 (e i))
      (w := w) (u := u) (v := v)
    · simpa [w,e,role1] using hout
    · simpa [w,e,role1] using hheavy
    · dsimp [u,v,e,role1]
      linear_combination ht
  · change m 0=5*m 1 at ha
    change m 1=m 2 at hb
    have hc := s.triangle.mass_center_w
    simp [Fin.sum_univ_succ] at hc
    rw [ha,← hb] at hc
    push_cast at hc
    have hmC : (m 1 : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hm 1)
    have hc0 : 5*s.triangle.w 0+s.triangle.w 1+s.triangle.w 2=0 := by
      apply mul_left_cancel₀ hmC
      linear_combination hc
    obtain ⟨hout,hheavy⟩ := centered3 hk d.difference01 d.difference02 hc0
    let e : Fin 3 ≃ Fin 3 := role3
    let w : Fin 3 → ℂ := fun i => s.triangle.w (e i)
    let u : Fin 3 → ℂ := fun i => s.cross 0 (e i)
    let v : Fin 3 → ℂ := fun i => s.cross 1 (e i)
    have ht := s.cross_torque
    simp [Fin.sum_univ_succ] at ht
    rw [ha,← hb] at ht
    push_cast at ht
    apply false_of_ordered_pair_triangle_torque (hm 3) (hm 4) (hm 1)
      (s.pairZ_ne_zero 0) (fun i => s.w_ne_zero (e i)) s.pair_balance
      (fun i => s.cross_square 0 (e i)) (fun i => s.cross_square 1 (e i))
      (w := w) (u := u) (v := v)
    · simpa [w,e,role3] using hout
    · simpa [w,e,role3] using hheavy
    · dsimp [u,v,e,role3]
      linear_combination ht

theorem PhysicalEulerLimit.transverse_ne_zero {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
    {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
    (s : PhysicalEulerLimit m q l I0) (hm : ∀ i, 0 < m i) :
    transverseEigenvalue s.triangle ≠ 0 := by
  intro hell
  exact false_of_certificate_ell_zero s.toFiveBodySource18Certificate s.signedEuler hm hell

end CentralConfigurations.FiveBody.D2.EllZero
