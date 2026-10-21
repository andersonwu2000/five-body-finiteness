import CentralConfigurations.Diagrams.TriangleOrders
import CentralConfigurations.Diagrams.ForceComparisonRules
import CentralConfigurations.Asymptotics.OrderTrichotomy
import CentralConfigurations.Asymptotics.SequenceOrders

/-!
# The skew-path step used in Proposition 4.15

Two consecutive same-color strokes with comparable same-color separations
force the closing stroke. Hence a nonclosed path has unequal separation
orders on a further subsequence. This extraction is explicit: the proof does
not assume arbitrary ratios already have limits on the given sequence.
-/

namespace CentralConfigurations

open Filter Asymptotics

namespace PairEstimateData

variable (p r : PairEstimateData)

theorem inv_z_fourth_from_forces (t : ℕ) :
    p.wForce t ^ 3 * (p.zForce t)⁻¹ = (p.z t)⁻¹ ^ 4 := by
  have h : p.wForce t ^ 3 = p.zForce t * (p.z t)⁻¹ ^ 4 :=
    p.swap.zForce_cube_opposite t
  rw [h]
  field_simp [p.zForce_ne_zero t]

theorem z_theta_of_force_pair
    (hz : p.zForce =Θ[atTop] r.zForce) (hw : p.wForce =Θ[atTop] r.wForce) :
    p.z =Θ[atTop] r.z := by
  have hp : (fun t => (p.z t)⁻¹ ^ 4) =Θ[atTop] (fun t => (r.z t)⁻¹ ^ 4) :=
    theta_congr_pointwise ((hw.pow 3).mul hz.inv)
      (fun t => p.inv_z_fourth_from_forces t) (fun t => r.inv_z_fourth_from_forces t)
  simpa only [inv_inv] using (theta_of_powers (by decide : (4 : ℕ) ≠ 0) hp).inv

end PairEstimateData

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem comparable_z_path_closes (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : l.z.force i j ≠ 0) (h₂ : l.z.force j k ≠ 0)
    (hz : (fun t => (q t).z i - (q t).z j) =Θ[atTop]
      (fun t => (q t).z j - (q t).z k)) : l.z.force i k ≠ 0 := by
  let p := ZWSystem.pairEstimateData q hb i j hij
  let r := ZWSystem.pairEstimateData q hb j k hjk
  let s := ZWSystem.pairEstimateData q hb i k hik
  have hp := (l.pair_z_stroke_iff hb i j hij).mpr h₁
  have hr := (l.pair_z_stroke_iff hb j k hjk).mpr h₂
  have hw := p.w_theta_of_z r (hp.trans hr.symm) hz
  have hzs : s.z =O[atTop] p.z :=
    ((isBigO_refl p.z atTop).add hz.2).congr_left (fun t => by
      change ((q t).z i - (q t).z j) + ((q t).z j - (q t).z k) =
        (q t).z i - (q t).z k
      ring)
  have hws : s.w =O[atTop] p.w :=
    ((isBigO_refl p.w atTop).add hw.2).congr_left (fun t => by
      change ((q t).w i - (q t).w j) + ((q t).w j - (q t).w k) =
        (q t).w i - (q t).w k
      ring)
  exact (l.pair_z_stroke_iff hb i k hik).mp
    ⟨s.zForce_upper, hp.2.trans (s.force_reverse_bound p hzs hws)⟩

theorem z_path_not_theta (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : l.z.force i j ≠ 0) (h₂ : l.z.force j k ≠ 0) (h₃ : l.z.force i k = 0) :
    ¬ ((fun t => (q t).z i - (q t).z j) =Θ[atTop]
      (fun t => (q t).z j - (q t).z k)) :=
  fun h => l.comparable_z_path_closes hb i j k hij hjk hik h₁ h₂ h h₃

theorem z_path_opposite_forces_not_theta (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : l.z.force i j ≠ 0) (h₂ : l.z.force j k ≠ 0) (h₃ : l.z.force i k = 0) :
    ¬ ((fun t => (q t).wForce i j) =Θ[atTop] (fun t => (q t).wForce j k)) := by
  intro hw
  exact l.z_path_not_theta hb i j k hij hjk hik h₁ h₂ h₃
    ((ZWSystem.pairEstimateData q hb i j hij).z_theta_of_force_pair
      (ZWSystem.pairEstimateData q hb j k hjk)
      (l.zForce_theta_of_strokes hb i j j k hij hjk h₁ h₂) hw)

theorem z_path_skew_subsequence (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (h₁ : l.z.force i j ≠ 0) (h₂ : l.z.force j k ≠ 0) (h₃ : l.z.force i k = 0) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (((fun t => (q (φ t)).z i - (q (φ t)).z j) =o[atTop]
        (fun t => (q (φ t)).z j - (q (φ t)).z k)) ∨
       ((fun t => (q (φ t)).z j - (q (φ t)).z k) =o[atTop]
        (fun t => (q (φ t)).z i - (q (φ t)).z j))) := by
  obtain ⟨φ, hφ, ht⟩ := exists_simultaneous_order_trichotomy
    (fun _ : Unit => fun t => (q t).z i - (q t).z j)
    (fun _ : Unit => fun t => (q t).z j - (q t).z k)
    (fun _ => Eventually.of_forall fun t => (q t).z_separation_ne_zero hjk)
  refine ⟨φ, hφ, ?_⟩
  rcases ht () with h | h | h
  · exact Or.inl h
  · exact ((l.comp φ hφ.tendsto_atTop).z_path_not_theta (fun t => hb (φ t))
      i j k hij hjk hik h₁ h₂ h₃ h).elim
  · exact Or.inr h

end ScaledZWLimit
end CentralConfigurations
