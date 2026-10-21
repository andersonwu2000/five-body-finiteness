import CentralConfigurations.FiveBody.Source19Mass
import CentralConfigurations.Model.FixedPotentialLevel
import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace CentralConfigurations.FiveBody.D6
noncomputable section
open Filter Asymptotics
open scoped Topology

/-- An exact reciprocal rotation of an actual system. Both chosen long
differences become 2/time. No dilation or symmetry constraint is imposed. -/
structure PairGauge {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) where
  rotation : ℂ
  rotation_ne : rotation≠0
  time : ℂ
  time_ne : time≠0
  rotation_sq : rotation^2=(q.w 0-q.w 1)/(q.z 3-q.z 4)
  time_eq : time=2/(rotation*(q.z 3-q.z 4))

noncomputable def pairGauge {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) : PairGauge q := by
  let hroot := IsAlgClosed.exists_pow_nat_eq ((q.w 0-q.w 1)/(q.z 3-q.z 4)) (by decide : 0<2)
  let α := Classical.choose hroot
  have hα : α^2=(q.w 0-q.w 1)/(q.z 3-q.z 4) := Classical.choose_spec hroot
  have ha : α≠0 := by
    intro h
    have hh := div_ne_zero (q.w_separation_ne_zero (by decide : (0:Fin 5)≠1))
      (q.z_separation_ne_zero (by decide : (3:Fin 5)≠4))
    simp [h] at hα
    exact hh hα.symm
  exact ⟨α,ha,2/(α*(q.z 3-q.z 4)),div_ne_zero (by norm_num)
    (mul_ne_zero ha (q.z_separation_ne_zero (by decide))),hα,rfl⟩

def PairGauge.normalized {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) :=
  q.rescale g.rotation g.rotation_ne

theorem PairGauge.z_difference {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) :
    g.normalized.z 3-g.normalized.z 4=2/g.time := by
  dsimp [PairGauge.normalized,ZWSystem.rescale]
  rw [g.time_eq]
  field_simp [g.rotation_ne,q.z_separation_ne_zero (by decide : (3:Fin 5)≠4)]

theorem PairGauge.w_difference {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) :
    g.normalized.w 0-g.normalized.w 1=2/g.time := by
  dsimp [PairGauge.normalized,ZWSystem.rescale]
  rw [g.time_eq]
  have he : g.rotation^2*(q.z 3-q.z 4)=q.w 0-q.w 1 := by
    rw [g.rotation_sq]
    field_simp [q.z_separation_ne_zero (by decide : (3:Fin 5)≠4)]
  field_simp [g.rotation_ne,q.z_separation_ne_zero (by decide : (3:Fin 5)≠4)]
  linear_combination -he

theorem PairGauge.potential {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) :
    g.normalized.toNormalized.potential=q.toNormalized.potential := rfl

theorem theta_of_square_ratio {f a : ℕ → ℂ} (_ha : ∀ t, a t≠0) {v : ℂ} (hv : v≠0)
    (h : Tendsto (fun t => (f t/a t)^2) atTop (𝓝 v)) : f =Θ[atTop] a := by
  have ht : (fun t => f t^2) =Θ[atTop] (fun t => a t^2) := by
    apply IsTheta.symm
    apply isTheta_of_div_tendsto_nhds_ne_zero _ hv
    simpa only [div_pow] using h
  exact ⟨IsBigO.of_pow (by decide : 2≠0) ht.1,IsBigO.of_pow (by decide : 2≠0) ht.2⟩

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (g : ∀ t, PairGauge (q t))
  (hz : l.z.position 3≠l.z.position 4) (hw : l.w.position 0≠l.w.position 1)
include l hz hw

omit hw in
theorem rotation_square_limit : Tendsto (fun t => (g t).rotation^2) atTop
    (𝓝 ((l.w.position 0-l.w.position 1)/(l.z.position 3-l.z.position 4))) := by
  have h := ((l.w_position 0).sub (l.w_position 1)).div
    ((l.z_position 3).sub (l.z_position 4)) (sub_ne_zero.mpr hz)
  exact h.congr (fun t => by
    dsimp only [Pi.div_apply]
    rw [(g t).rotation_sq]
    rw [← mul_sub,← mul_sub]
    field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide) t])

theorem rotation_bounded : (fun t => (g t).rotation) =O[atTop] (fun _ => (1:ℂ)) ∧
    (fun t => ((g t).rotation)⁻¹) =O[atTop] (fun _ => (1:ℂ)) := by
  have h := rotation_square_limit l g hz
  constructor
  · apply IsBigO.of_pow (by decide : 2≠0)
    change (fun t => (g t).rotation^2) =O[atTop] (fun _ => (1:ℂ)^2)
    simpa only [one_pow] using h.isBigO_one ℂ
  · have hh := h.inv₀ (div_ne_zero (sub_ne_zero.mpr hw) (sub_ne_zero.mpr hz))
    apply IsBigO.of_pow (by decide : 2≠0)
    change (fun t => ((g t).rotation)⁻¹^2) =O[atTop] (fun _ => (1:ℂ)^2)
    simpa only [one_pow,inv_pow] using hh.isBigO_one ℂ

theorem time_scale : (fun t => (g t).time) =Θ[atTop] (fun t => (q t).inverseScale) := by
  have hs := ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)
  have hc : (l.z.position 3-l.z.position 4)*(l.w.position 0-l.w.position 1)≠0 :=
    mul_ne_zero (sub_ne_zero.mpr hz) (sub_ne_zero.mpr hw)
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (4:ℂ)) atTop (𝓝 4)).div
    (((l.z_position 3).sub (l.z_position 4)).mul ((l.w_position 0).sub (l.w_position 1))) hc
  apply theta_of_square_ratio hs (div_ne_zero (by norm_num : (4:ℂ)≠0) hc)
  exact h.congr (fun t => by
    dsimp only [Pi.div_apply]
    rw [(g t).time_eq]
    simp only [div_pow,mul_pow,(g t).rotation_sq]
    rw [← mul_sub,← mul_sub]
    field_simp [hs t,(q t).z_separation_ne_zero (by decide : (3:Fin 5)≠4),
      (q t).w_separation_ne_zero (by decide : (0:Fin 5)≠1)]
    ring)

theorem time_zero (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    Tendsto (fun t => (g t).time) atTop (𝓝 0) :=
  (time_scale l g hz hw).1.trans_tendsto ha

end
end CentralConfigurations.FiveBody.D6
