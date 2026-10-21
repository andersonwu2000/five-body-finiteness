import CentralConfigurations.FiveBody.OrdinaryD7Orders
import CentralConfigurations.Model.ZWMassCenter

/-! Exact D7 center response from the actual forces. All four crossed
forces remain in the identity. Cancellations and signed sheets are allowed. -/

namespace CentralConfigurations.FiveBody.Ordinary.D7
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators

def upperOppForce {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass) : ℕ → ℂ :=
  fun t => (q t).wForce 0 1
def lowerOppForce {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass) : ℕ → ℂ :=
  fun t => (q t).zForce 2 3

theorem separation_bigO_force_of_bounded_radius (p : PairEstimateData)
    (hr : p.radius =O[atTop] (fun _ => (1 : ℂ))) : p.z =O[atTop] p.zForce := by
  have h := (hr.pow 3).mul (isBigO_refl p.zForce atTop)
  apply h.congr
  · intro t
    dsimp [PairEstimateData.radius, PairEstimateData.zForce]
    field_simp [p.delta_ne_zero t]
  · intro t
    simp

theorem center_z_identity {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass) :
    (mass 2 + mass 3) * q.z 4 =
      -(mass 4 * (mass 2 * q.zForce 4 2 + mass 3 * q.zForce 4 3)) -
      (mass 0 * mass 2 * q.zForce 0 2 + mass 0 * mass 3 * q.zForce 0 3 +
       mass 1 * mass 2 * q.zForce 1 2 + mass 1 * mass 3 * q.zForce 1 3) -
      mass 2 * (q.z 2 - q.z 4) - mass 3 * (q.z 3 - q.z 4) := by
  have h0 := q.force_z 0
  have h1 := q.force_z 1
  have h4 := q.force_z 4
  have hc := q.mass_center_z
  simp [Fin.sum_univ_succ, q.delta_diagonal] at h0 h1 h4 hc
  dsimp [ZWSystem.zForce]
  rw [q.delta_symm 1 0] at h1
  rw [q.delta_symm 4 0, q.delta_symm 4 1] at h4
  linear_combination hc - mass 0 * h0 - mass 1 * h1 - mass 4 * h4

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
  (hd : l.diagramCode = akDiagram 6)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include hb hd ha

theorem lower_internal_force_bound (i : Fin 5) (hi : i ∈ ({2,3} : Finset (Fin 5))) :
    (fun t => (q t).zForce i 4) =O[atTop] lowerOppForce q := by
  have hi4 : i ≠ 4 := by fin_cases i <;> simp_all [Fin.ext_iff]
  let p := ZWSystem.pairEstimateData q hb 2 3 (by decide)
  let r := ZWSystem.pairEstimateData q hb i 4 hi4
  have ht := lower_orders l hb hd i hi
  exact p.force_reverse_bound r ht.1.2 ht.2.2

theorem upper_internal_force_bound (i : Fin 5) (hi : i ∈ ({0,1} : Finset (Fin 5))) :
    (fun t => (q t).wForce i 4) =O[atTop] upperOppForce q := by
  have hi4 : i ≠ 4 := by fin_cases i <;> simp_all [Fin.ext_iff]
  let p := ZWSystem.pairEstimateData q hb 0 1 (by decide)
  let r := ZWSystem.pairEstimateData q hb i 4 hi4
  have ht := upper_orders l hb hd i hi
  exact p.swap.force_reverse_bound r.swap ht.2.2 ht.1.2

theorem cross_zForce_bound (i j : Fin 5) (hi : i ∈ ({0,1} : Finset (Fin 5)))
    (hj : j ∈ ({2,3} : Finset (Fin 5))) :
    (fun t => (q t).zForce i j) =O[atTop] lowerOppForce q := by
  have hij : i ≠ j := by fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
  let p := ZWSystem.pairEstimateData q hb 2 3 (by decide)
  let r := ZWSystem.pairEstimateData q hb i j hij
  have hcross := cross_orders l hb hd ha i j hi hj
  have hlower := lower_orders l hb hd 2 (by decide)
  have hsmall := lower_z_littleO_upper l hb hd ha 2 (by decide)
  have hz : p.z =O[atTop] r.z := hlower.1.2.trans (hsmall.isBigO.trans hcross.1.2)
  exact p.force_reverse_bound r hz hcross.2.2

theorem cross_wForce_bound (i j : Fin 5) (hi : i ∈ ({0,1} : Finset (Fin 5)))
    (hj : j ∈ ({2,3} : Finset (Fin 5))) :
    (fun t => (q t).wForce i j) =O[atTop] upperOppForce q := by
  have hij : i ≠ j := by fin_cases i <;> fin_cases j <;> simp_all [Fin.ext_iff]
  let p := ZWSystem.pairEstimateData q hb 0 1 (by decide)
  let r := ZWSystem.pairEstimateData q hb i j hij
  have hcross := cross_orders l hb hd ha i j hi hj
  have hupper := upper_orders l hb hd 0 (by decide)
  have hsmall := upper_w_littleO_lower l hb hd ha 0 (by decide)
  have hw : p.w =O[atTop] r.w := hupper.2.2.trans (hsmall.isBigO.trans hcross.2.2)
  exact p.swap.force_reverse_bound r.swap hw hcross.1.2

theorem lower_z_separation_force_bound (i : Fin 5) (hi : i ∈ ({2,3} : Finset (Fin 5))) :
    zsep q i 4 =O[atTop] lowerOppForce q := by
  let p := ZWSystem.pairEstimateData q hb 2 3 (by decide)
  have hw := lower_w_force l hb hd 2 3 (by decide) (by decide) (by decide)
  have hr := p.swap.stroke_radius_upper ((l.pair_w_stroke_iff hb 2 3 (by decide)).mpr hw)
  exact (lower_orders l hb hd i hi).1.1.trans (separation_bigO_force_of_bounded_radius p hr)

theorem upper_w_separation_force_bound (i : Fin 5) (hi : i ∈ ({0,1} : Finset (Fin 5))) :
    wsep q i 4 =O[atTop] upperOppForce q := by
  let p := ZWSystem.pairEstimateData q hb 0 1 (by decide)
  have hz := upper_z_force l hb hd 0 1 (by decide) (by decide) (by decide)
  have hr := p.stroke_radius_upper ((l.pair_z_stroke_iff hb 0 1 (by decide)).mpr hz)
  exact (upper_orders l hb hd i hi).2.1.trans (separation_bigO_force_of_bounded_radius p.swap hr)

theorem center_z_bound (hml : mass 2 + mass 3 ≠ 0) :
    (fun t => (q t).z 4) =O[atTop] lowerOppForce q := by
  have hf2 := (lower_internal_force_bound l hb hd ha 2 (by decide)).neg_left
  have hf3 := (lower_internal_force_bound l hb hd ha 3 (by decide)).neg_left
  have hf2' : (fun t => (q t).zForce 4 2) =O[atTop] lowerOppForce q :=
    hf2.congr_left (fun t => ((q t).zForce_antisymm 4 2).symm)
  have hf3' : (fun t => (q t).zForce 4 3) =O[atTop] lowerOppForce q :=
    hf3.congr_left (fun t => ((q t).zForce_antisymm 4 3).symm)
  have hB := ((hf2'.const_mul_left (mass 2)).add (hf3'.const_mul_left (mass 3))).const_mul_left (mass 4)
  have hC := (((cross_zForce_bound l hb hd ha 0 2 (by decide) (by decide)).const_mul_left (mass 0 * mass 2)).add
    ((cross_zForce_bound l hb hd ha 0 3 (by decide) (by decide)).const_mul_left (mass 0 * mass 3))).add
    (((cross_zForce_bound l hb hd ha 1 2 (by decide) (by decide)).const_mul_left (mass 1 * mass 2)).add
    ((cross_zForce_bound l hb hd ha 1 3 (by decide) (by decide)).const_mul_left (mass 1 * mass 3)))
  have h2 := (lower_z_separation_force_bound l hb hd ha 2 (by decide)).const_mul_left (mass 2)
  have h3 := (lower_z_separation_force_bound l hb hd ha 3 (by decide)).const_mul_left (mass 3)
  have hh := ((hB.neg_left.sub hC).sub h2).sub h3
  apply (isBigO_const_mul_left_iff hml).mp
  exact hh.congr_left (fun t => by rw [center_z_identity]; dsimp [zsep]; ring)

end
end CentralConfigurations.FiveBody.Ordinary.D7
