import CentralConfigurations.Enumeration.FiveBodySourceData
import CentralConfigurations.Enumeration.NormalizedSearch
import CentralConfigurations.FiveBody.D9Orders
import CentralConfigurations.Asymptotics.ClusterPairLimits
import CentralConfigurations.Diagrams.BoundaryCuts

namespace CentralConfigurations.FiveBody.PairEnergy
open Filter Asymptotics
open scoped Topology BigOperators
set_option maxRecDepth 10000

/-- Pair 01 is z-circled, the other three vertices are uncircled. The triple
has simple w-edges for AK D1, double edges for AK D4. -/
def akDiagram (double : Bool) : DiagramCode 5 :=
  (BinaryMatrixCode.fromMask 5 (if double then 11299 else 35),
   BinaryMatrixCode.fromMask 5 11264)

theorem chang5_to_akD1 :
    DiagramCode.transform (fiveBodySourceDiagram 4) (Equiv.refl _) true = akDiagram false := by
  decide +kernel

theorem chang6_to_akD4 :
    DiagramCode.transform (fiveBodySourceDiagram 5) (Equiv.refl _) true = akDiagram true := by
  decide +kernel

theorem pair_z_circles (b : Bool) (i : Fin 5) (hi : i<2) :
    BinaryMatrixCode.decode (akDiagram b).1 i i = 1 := by
  revert b i
  decide +kernel

theorem triple_z_uncircled (b : Bool) (i : Fin 5) (hi : 2 ≤ i) :
    BinaryMatrixCode.decode (akDiagram b).1 i i = 0 := by
  revert b i
  decide +kernel

theorem all_w_uncircled (b : Bool) (i : Fin 5) :
    BinaryMatrixCode.decode (akDiagram b).2 i i = 0 := by
  cases b <;> fin_cases i <;> decide +kernel

theorem cross_z_absent (b : Bool) (i j : Fin 5) (hi : i<2) (hj : 2 ≤ j) :
    BinaryMatrixCode.decode (akDiagram b).1 i j = 0 := by
  revert b i j
  decide +kernel

theorem triangle_w_present (b : Bool) (i j : Fin 5) (hi : 2 ≤ i) (hj : 2 ≤ j) (hne : i ≠ j) :
    BinaryMatrixCode.decode (akDiagram b).2 i j = 1 := by
  revert b i j
  decide +kernel

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass} {b : Bool}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hd : l.diagramCode=akDiagram b)
include l hd

theorem matrices : l.z.matrix=BinaryMatrixCode.decode (akDiagram b).1 ∧
    l.w.matrix=BinaryMatrixCode.decode (akDiagram b).2 := by
  constructor
  · have h := congrArg Prod.fst hd
    change BinaryMatrixCode.encode l.z.matrix = (akDiagram b).1 at h
    rw [← h]
    exact (BinaryMatrixCode.decode_encode _ l.z.matrix_binary l.z.matrix_symm).symm
  · have h := congrArg Prod.snd hd
    change BinaryMatrixCode.encode l.w.matrix = (akDiagram b).2 at h
    rw [← h]
    exact (BinaryMatrixCode.decode_encode _ l.w.matrix_binary l.w.matrix_symm).symm

theorem pair_z_positions_ne (i : Fin 5) (hi : i<2) : l.z.position i ≠ 0 := by
  have hh : l.z.matrix i i=1 := by rw [(matrices l hd).1]; exact pair_z_circles b i hi
  simpa [OneColorLimit.matrix,OneColorLimit.Incident] using hh

theorem triple_z_positions_zero (i : Fin 5) (hi : 2 ≤ i) : l.z.position i=0 := by
  have hh : l.z.matrix i i=0 := by rw [(matrices l hd).1]; exact triple_z_uncircled b i hi
  simpa [OneColorLimit.matrix,OneColorLimit.Incident] using hh

theorem w_positions_zero (i : Fin 5) : l.w.position i=0 := by
  have hh : l.w.matrix i i=0 := by rw [(matrices l hd).2]; exact all_w_uncircled b i
  simpa [OneColorLimit.matrix,OneColorLimit.Incident] using hh

theorem cross_z_force_zero (i j : Fin 5) (hi : i<2) (hj : 2 ≤ j) : l.z.force i j=0 := by
  have hne : i ≠ j := by omega
  have hh : l.z.matrix i j=0 := by rw [(matrices l hd).1]; exact cross_z_absent b i j hi hj
  simpa [OneColorLimit.matrix,OneColorLimit.Incident,hne] using hh

theorem triangle_w_force_ne (i j : Fin 5) (hi : 2 ≤ i) (hj : 2 ≤ j) (hne : i ≠ j) :
    l.w.force i j ≠ 0 := by
  have hh : l.w.matrix i j=1 := by
    rw [(matrices l hd).2]; exact triangle_w_present b i j hi hj hne
  simpa [OneColorLimit.matrix,OneColorLimit.Incident,hne] using hh

theorem pair_balances : l.z.position 0=mass 1*l.z.force 0 1 ∧
    l.z.position 1= -(mass 0*l.z.force 0 1) := by
  constructor
  · have h := l.z.balance 0
    simpa [Fin.sum_univ_succ,l.z.diagonal,
      cross_z_force_zero l hd 0 2 (by decide) (by decide),
      cross_z_force_zero l hd 0 3 (by decide) (by decide),
      cross_z_force_zero l hd 0 4 (by decide) (by decide)] using h
  · have h := l.z.balance 1
    simpa [Fin.sum_univ_succ,l.z.diagonal,l.z.antisymm 1 0,
      cross_z_force_zero l hd 1 2 (by decide) (by decide),
      cross_z_force_zero l hd 1 3 (by decide) (by decide),
      cross_z_force_zero l hd 1 4 (by decide) (by decide)] using h

theorem pair_force_ne : l.z.force 0 1 ≠ 0 := by
  intro h
  have hh := (pair_balances l hd).1
  simp [h] at hh
  exact pair_z_positions_ne l hd 0 (by decide) hh

omit l hd

noncomputable abbrev A (q : ℕ → ZWSystem ℂ 5 mass) := fun t => (q t).inverseScale
abbrev D (q : ℕ → ZWSystem ℂ 5 mass) (i j : Fin 5) :=
  fun t => ((q t).z i-(q t).z j)*((q t).w i-(q t).w j)

theorem scale_ne (t : ℕ) : A q t ≠ 0 :=
  inv_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
    ((q t).zVector_ne_zero 0 1 (by decide))))

theorem delta_ne (i j : Fin 5) (hij : i≠j) (t : ℕ) : (q t).delta i j≠0 := by
  intro h
  have hh := (q t).distance i j hij
  simp [h] at hh

theorem metric_inv_delta (i j : Fin 5) (hij : i≠j) (t : ℕ) :
    D q i j t = ((q t).delta i j)⁻¹^2 := by
  apply (mul_left_cancel₀ (pow_ne_zero 2 (delta_ne i j hij t)))
  rw [show (q t).delta i j^2 * D q i j t=1 from (q t).distance i j hij]
  field_simp [delta_ne (q := q) i j hij t]

end CentralConfigurations.FiveBody.PairEnergy
