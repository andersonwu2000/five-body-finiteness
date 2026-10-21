import CentralConfigurations.FiveBody.D2Resonance.ActualCases
import CentralConfigurations.FiveBody.D2Resonance.CenteredGeometry
import CentralConfigurations.FiveBody.D2EllZero.RoleOrders

namespace CentralConfigurations.FiveBody.D2.Resonance
open Exceptional EllZero
set_option maxHeartbeats 2000000

theorem original_cross_transport {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass)
    (t : ℕ) (p : Fin 2) (i : Fin 3) :
    (q t).delta (fullRole0 (Fin.natAdd 3 p)) (fullRole0 (i.castLE (by decide)))=
      (q t).delta (Fin.natAdd 3 p) ((role0 i).castLE (by decide)) ∧
    (q t).delta (fullRole1 (Fin.natAdd 3 p)) (fullRole1 (i.castLE (by decide)))=
      (q t).delta (Fin.natAdd 3 p) ((role1 i).castLE (by decide)) ∧
    (q t).delta (fullRole3 (Fin.natAdd 3 p)) (fullRole3 (i.castLE (by decide)))=
      (q t).delta (Fin.natAdd 3 p) ((role3 i).castLE (by decide)) := by
  obtain ⟨h0,h1,h3⟩ := full_roles_fix_pair p
  rw [h0,h1,h3,full_role0_triangle,full_role1_triangle,full_role3_triangle]
  exact ⟨rfl,rfl,rfl⟩

theorem centered0 {mass : Fin 3 → ℂ} {r : ZWSystem ℂ 3 mass}
    (d : GapData r) (hr : 2*d.x.re=resonanceShift) (hn : Complex.normSq d.x=resonanceShift)
    (hc : r.w 0+(resonanceWeight:ℂ)*r.w 1+r.w 2=0) :
    ‖r.w 0‖^2=‖r.w 2‖^2 ∧ 4*‖r.w 1‖^2<‖r.w 0‖^2 :=
  centered_resonance_norms d.scale_ne_zero hr hn d.difference01 d.difference02 hc

theorem centered1 {mass : Fin 3 → ℂ} {r : ZWSystem ℂ 3 mass}
    (d : GapData r) (hr : 2*(1/d.x).re=resonanceShift)
    (hn : Complex.normSq (1/d.x)=resonanceShift)
    (hc : r.w 0+r.w 1+(resonanceWeight:ℂ)*r.w 2=0) :
    ‖r.w 0‖^2=‖r.w 1‖^2 ∧ 4*‖r.w 2‖^2<‖r.w 0‖^2 := by
  let w : Fin 3 → ℂ := fun i => r.w (role1 i)
  have hg : d.scale*d.x≠0 := mul_ne_zero d.scale_ne_zero d.x_ne_zero
  have h01 : w 1-w 0=d.scale*d.x := by exact d.difference02
  have h02 : w 2-w 0=(d.scale*d.x)*(1/d.x) := by
    change r.w 1-r.w 0=(d.scale*d.x)*(1/d.x)
    rw [d.difference01]
    field_simp [d.x_ne_zero]
  have hcenter : w 0+(resonanceWeight:ℂ)*w 1+w 2=0 := by
    change r.w 0+(resonanceWeight:ℂ)*r.w 2+r.w 1=0
    linear_combination hc
  simpa [w,role1] using centered_resonance_norms hg hr hn h01 h02 hcenter

theorem centered3 {mass : Fin 3 → ℂ} {r : ZWSystem ℂ 3 mass}
    (d : GapData r) (hr : 2*(1-d.x).re=resonanceShift)
    (hn : Complex.normSq (1-d.x)=resonanceShift)
    (hc : (resonanceWeight:ℂ)*r.w 0+r.w 1+r.w 2=0) :
    ‖r.w 1‖^2=‖r.w 2‖^2 ∧ 4*‖r.w 0‖^2<‖r.w 1‖^2 := by
  let w : Fin 3 → ℂ := fun i => r.w (role3 i)
  have hg : -d.scale≠0 := neg_ne_zero.mpr d.scale_ne_zero
  have h01 : w 1-w 0=-d.scale := by
    change r.w 0-r.w 1=-d.scale
    linear_combination -d.difference01
  have h02 : w 2-w 0=(-d.scale)*(1-d.x) := by
    change r.w 2-r.w 1=(-d.scale)*(1-d.x)
    linear_combination d.difference02-d.difference01
  have hcenter : w 0+(resonanceWeight:ℂ)*w 1+w 2=0 := by
    change r.w 1+(resonanceWeight:ℂ)*r.w 0+r.w 2=0
    linear_combination hc
  simpa [w,role3] using centered_resonance_norms hg hr hn h01 h02 hcenter

end CentralConfigurations.FiveBody.D2.Resonance
