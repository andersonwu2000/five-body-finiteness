import CentralConfigurations.Enumeration.FiveBodySourceData
import CentralConfigurations.Enumeration.NormalizedSearch
import CentralConfigurations.FiveBody.SimpleMassRelations
import CentralConfigurations.FiveBody.D9Orders
import CentralConfigurations.Asymptotics.PairEstimates
import CentralConfigurations.Asymptotics.EpsilonOrderScales
import CentralConfigurations.Asymptotics.FiniteLimitExtraction

namespace CentralConfigurations.FiveBody.D5
open Filter Asymptotics
open scoped Topology BigOperators
set_option maxRecDepth 10000

def akD5Diagram : DiagramCode 5 :=
  (BinaryMatrixCode.fromMask 5 70, BinaryMatrixCode.fromMask 5 70)

def canonicalToAKRoles : Equiv.Perm (Fin 5) where
  toFun i := ![2,3,4,0,1] i
  invFun i := ![3,4,0,1,2] i
  left_inv := by decide +kernel
  right_inv := by decide +kernel

theorem chang3_to_akD5 :
    DiagramCode.transform (fiveBodySourceDiagram 2) canonicalToAKRoles false = akD5Diagram := by
  decide +kernel

theorem akD5_support (i j : Fin 5) :
    BinaryMatrixCode.decode akD5Diagram.1 i j =
      if i ≠ j ∧ i < 3 ∧ j < 3 then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide +kernel

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}

abbrev Z (q : ℕ → ZWSystem ℂ 5 mass) (i j : Fin 5) := fun t => (q t).z i-(q t).z j
abbrev W (q : ℕ → ZWSystem ℂ 5 mass) (i j : Fin 5) := fun t => (q t).w i-(q t).w j
abbrev D (q : ℕ → ZWSystem ℂ 5 mass) (i j : Fin 5) := fun t => Z q i j t * W q i j t
noncomputable def eps (q : ℕ → ZWSystem ℂ 5 mass) : ℕ → ℂ := fun t => ((q t).epsilon : ℂ)

theorem eps_ne (t : ℕ) : eps q t ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt ((q t).epsilon_pos 0 1 (by decide)))

theorem eps_sq (t : ℕ) : eps q t^2 = (q t).inverseScale := by
  have h := congrArg Inv.inv ((q t).epsilon_scale)
  simpa only [inv_pow, inv_inv, ZWSystem.inverseScale] using h

theorem eps_inv_sq (t : ℕ) : (eps q t)⁻¹^2 = (‖(q t).zVector‖ : ℂ) := (q t).epsilon_scale

theorem eps_zero (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    Tendsto (eps q) atTop (𝓝 0) := by
  apply D9.zero_of_power (n := 2) (by decide)
  simpa only [eps_sq] using ha

variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
  (hd : l.diagramCode = akD5Diagram)
include l hd

theorem matrices : l.z.matrix = BinaryMatrixCode.decode akD5Diagram.1 ∧
    l.w.matrix = BinaryMatrixCode.decode akD5Diagram.1 := by
  constructor
  · have h := congrArg Prod.fst hd
    change BinaryMatrixCode.encode l.z.matrix = akD5Diagram.1 at h
    rw [← h]
    exact (BinaryMatrixCode.decode_encode _ l.z.matrix_binary l.z.matrix_symm).symm
  · have h := congrArg Prod.snd hd
    change BinaryMatrixCode.encode l.w.matrix = akD5Diagram.1 at h
    rw [← h]
    exact (BinaryMatrixCode.decode_encode _ l.w.matrix_binary l.w.matrix_symm).symm

theorem positions_zero (i : Fin 5) : l.z.position i=0 ∧ l.w.position i=0 := by
  have hz : l.z.matrix i i=0 := by rw [(matrices l hd).1,akD5_support]; simp
  have hw : l.w.matrix i i=0 := by rw [(matrices l hd).2,akD5_support]; simp
  simpa [OneColorLimit.matrix,OneColorLimit.Incident] using And.intro hz hw

theorem positions_small (i : Fin 5) :
    (fun t => (q t).z i) =o[atTop] (fun t => (eps q t)⁻¹^2) ∧
    (fun t => (q t).w i) =o[atTop] (fun t => (eps q t)⁻¹^2) := by
  have hn (t) : (‖(q t).zVector‖ : ℂ) ≠ 0 := by
    rw [← eps_inv_sq]; exact pow_ne_zero 2 (inv_ne_zero (eps_ne t))
  simpa only [eps_inv_sq] using And.intro
    ((normalized_littleO_iff hn (l.z_position i)).2 (positions_zero l hd i).1)
    ((normalized_littleO_iff hn (l.w_position i)).2 (positions_zero l hd i).2)

include hb
theorem triangle_orders (i j : Fin 5) (hi : i<3) (hj : j<3) :
    Z q i j =O[atTop] eps q ∧ W q i j =O[atTop] eps q := by
  by_cases hne : i=j
  · subst j
    constructor <;> exact (isBigO_zero (E' := ℂ) (eps q) atTop).congr_left (fun t => by simp)
  have hz : l.z.force i j ≠ 0 := by
    have h : l.z.matrix i j=1 := by rw [(matrices l hd).1,akD5_support]; simp [hi,hj,hne]
    simpa [OneColorLimit.matrix,OneColorLimit.Incident,hne] using h
  have hw : l.w.force i j ≠ 0 := by
    have h : l.w.matrix i j=1 := by rw [(matrices l hd).2,akD5_support]; simp [hi,hj,hne]
    simpa [OneColorLimit.matrix,OneColorLimit.Incident,hne] using h
  let p := ZWSystem.pairEstimateData q hb i j hne
  exact ⟨p.swap.stroke_w_upper ((l.pair_w_stroke_iff hb i j hne).2 hw),
    p.stroke_w_upper ((l.pair_z_stroke_iff hb i j hne).2 hz)⟩

end CentralConfigurations.FiveBody.D5
