import CentralConfigurations.Asymptotics.ForceOrderComparison

/-!
# Stroke hypotheses in the force-comparison rules

The nonzero leading coefficients provide the force bounds needed in rules
(6a,b,i,j) and (7a,b,i,j). These bridges apply the algebraic comparison lemmas
to actual balanced solution sequences; a stroke is not an assumed order code.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem zForce_theta_of_strokes (i j k m : Fin n) (hij : i ≠ j) (hkm : k ≠ m)
    (hi : l.z.force i j ≠ 0) (hk : l.z.force k m ≠ 0) :
    (fun t => (q t).zForce i j) =Θ[atTop] (fun t => (q t).zForce k m) :=
  ((l.pair_z_stroke_iff hb i j hij).mpr hi).trans
    ((l.pair_z_stroke_iff hb k m hkm).mpr hk).symm

theorem wForce_theta_of_strokes (i j k m : Fin n) (hij : i ≠ j) (hkm : k ≠ m)
    (hi : l.w.force i j ≠ 0) (hk : l.w.force k m ≠ 0) :
    (fun t => (q t).wForce i j) =Θ[atTop] (fun t => (q t).wForce k m) :=
  ((l.pair_w_stroke_iff hb i j hij).mpr hi).trans
    ((l.pair_w_stroke_iff hb k m hkm).mpr hk).symm

theorem zForce_littleO_of_absent_stroke (i j k m : Fin n) (hij : i ≠ j) (hkm : k ≠ m)
    (hi : l.z.force i j = 0) (hk : l.z.force k m ≠ 0) :
    (fun t => (q t).zForce i j) =o[atTop] (fun t => (q t).zForce k m) :=
  ((l.pair_z_absent_iff hb i j hij).mpr hi).trans_isTheta
    ((l.pair_z_stroke_iff hb k m hkm).mpr hk).symm

theorem wForce_littleO_of_absent_stroke (i j k m : Fin n) (hij : i ≠ j) (hkm : k ≠ m)
    (hi : l.w.force i j = 0) (hk : l.w.force k m ≠ 0) :
    (fun t => (q t).wForce i j) =o[atTop] (fun t => (q t).wForce k m) :=
  ((l.pair_w_absent_iff hb i j hij).mpr hi).trans_isTheta
    ((l.pair_w_stroke_iff hb k m hkm).mpr hk).symm

theorem zForce_littleO_of_w_separation_stroke (i j k m : Fin n)
    (hij : i ≠ j) (hkm : k ≠ m) (hk : l.w.force k m ≠ 0)
    (hw : (fun t => (q t).w k - (q t).w m) =o[atTop]
      (fun t => (q t).w i - (q t).w j)) :
    (fun t => (q t).zForce i j) =o[atTop] (fun t => (q t).zForce k m) := by
  let p := ZWSystem.pairEstimateData q hb i j hij
  let r := ZWSystem.pairEstimateData q hb k m hkm
  exact p.zForce_littleO_of_opposite_force r
    (p.wForce_upper.trans ((l.pair_w_stroke_iff hb k m hkm).mpr hk).2) hw

theorem wForce_littleO_of_z_separation_stroke (i j k m : Fin n)
    (hij : i ≠ j) (hkm : k ≠ m) (hk : l.z.force k m ≠ 0)
    (hz : (fun t => (q t).z k - (q t).z m) =o[atTop]
      (fun t => (q t).z i - (q t).z j)) :
    (fun t => (q t).wForce i j) =o[atTop] (fun t => (q t).wForce k m) := by
  let p := ZWSystem.pairEstimateData q hb i j hij
  let r := ZWSystem.pairEstimateData q hb k m hkm
  exact p.wForce_littleO_of_opposite_force r
    (p.zForce_upper.trans ((l.pair_z_stroke_iff hb k m hkm).mpr hk).2) hz

theorem zForce_theta_of_w_separation_strokes (i j k m : Fin n)
    (hij : i ≠ j) (hkm : k ≠ m) (hi : l.w.force i j ≠ 0) (hk : l.w.force k m ≠ 0)
    (hw : (fun t => (q t).w i - (q t).w j) =Θ[atTop]
      (fun t => (q t).w k - (q t).w m)) :
    (fun t => (q t).zForce i j) =Θ[atTop] (fun t => (q t).zForce k m) :=
  (ZWSystem.pairEstimateData q hb i j hij).zForce_theta_of_opposite_force
    (ZWSystem.pairEstimateData q hb k m hkm) (l.wForce_theta_of_strokes hb i j k m hij hkm hi hk) hw

theorem wForce_theta_of_z_separation_strokes (i j k m : Fin n)
    (hij : i ≠ j) (hkm : k ≠ m) (hi : l.z.force i j ≠ 0) (hk : l.z.force k m ≠ 0)
    (hz : (fun t => (q t).z i - (q t).z j) =Θ[atTop]
      (fun t => (q t).z k - (q t).z m)) :
    (fun t => (q t).wForce i j) =Θ[atTop] (fun t => (q t).wForce k m) :=
  (ZWSystem.pairEstimateData q hb i j hij).wForce_theta_of_opposite_force
    (ZWSystem.pairEstimateData q hb k m hkm) (l.zForce_theta_of_strokes hb i j k m hij hkm hi hk) hz

end ScaledZWLimit
end CentralConfigurations
