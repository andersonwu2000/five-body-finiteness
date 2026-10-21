import CentralConfigurations.Enumeration.RowOrderComparisons
import CentralConfigurations.Enumeration.LeadingRowOrders

/-!
# Certified comparisons used by MaxOrderZ and MaxOrderW

The executable functions take only finite diagram and order-domain data.
Their soundness theorems supply every premise from an actual balanced singular
sequence and an admitted order assignment. Both colors use the same decision
tree, with coordinate and leading-support inputs interchanged.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

def compareForceRow {n : ℕ} (A A' : BinaryMatrixCode n)
    (B B' : Fin n → Fin n → Finset (Fin 6)) (D : OrderBox (ROrderIndex n))
    (i j k : Fin n) : OrderComparison :=
  (compareLeadingFlags (A (upperIndex i j)) (A (upperIndex i k))).orElse
    (compareForceAlgebra (compareCoordinateRow B i j k) (compareCoordinateRow B' i j k)
      (compareOrderDomains (radiusDomainEntry D i j) (radiusDomainEntry D i k))
      (A' (upperIndex i j)) (A' (upperIndex i k)))

def comparePositionForceRow {n : ℕ} (A : BinaryMatrixCode n)
    (B : Fin n → Fin n → Finset (Fin 6)) (D : OrderBox (ROrderIndex n))
    (i j : Fin n) : OrderComparison :=
  (compareLeadingFlags (A (upperIndex i i)) (A (upperIndex i j))).orElse
    (comparePositionForceAlgebra (compareCoordinateRow B i i j)
      (compareOneToRadiusDomain (radiusDomainEntry D i j)))

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
variable (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode)
variable (D : OrderBox (ROrderIndex n)) (hD : D.Admits o.radiusCode)
include o hb hB hD

theorem compare_zForce_row_valid (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) :
    (compareForceRow l.diagramCode.1 l.diagramCode.2
      (fun a b => B (zwOrderSlot 0 a b)) (fun a b => B (zwOrderSlot 1 a b)) D i j k).Valid
      (fun t => (q t).zForce i j) (fun t => (q t).zForce i k) := by
  let p := ZWSystem.pairEstimateData q hb i j hij
  let r := ZWSystem.pairEstimateData q hb i k hik
  have hz := o.compare_z_row_valid B hB i j k
  have hw := o.compare_w_row_valid B hB i j k
  simp only [ZWSystem.zOrderValue, if_neg hij, if_neg hik] at hz
  simp only [ZWSystem.wOrderValue, if_neg hij, if_neg hik] at hw
  have hr := o.compare_radius_domains_valid D hD i j i k hij hik
  have hjflag : LeadingOrderFlag (l.diagramCode.2 (upperIndex i j)) p.wForce
      (fun t => (‖(q t).zVector‖ : ℂ)) := by
    simpa only [ZWSystem.wMaxTermValue, if_neg hij] using l.w_maxTerm_leadingFlag i₀ j₀ hij₀ i j
  have hkflag : LeadingOrderFlag (l.diagramCode.2 (upperIndex i k)) r.wForce
      (fun t => (‖(q t).zVector‖ : ℂ)) := by
    simpa only [ZWSystem.wMaxTermValue, if_neg hik] using l.w_maxTerm_leadingFlag i₀ j₀ hij₀ i k
  unfold compareForceRow
  apply OrderComparison.Valid.orElse
  · apply compareLeadingFlags_valid
    · simpa only [ZWSystem.zMaxTermValue, if_neg hij] using l.z_maxTerm_leadingFlag i₀ j₀ hij₀ i j
    · simpa only [ZWSystem.zMaxTermValue, if_neg hik] using l.z_maxTerm_leadingFlag i₀ j₀ hij₀ i k
  · refine p.compare_zForce_algebra_valid r _ _ _ _ _ hz hw hr ?_ ?_
    · intro h
      exact hkflag.isBigO.trans (hjflag.theta h).2
    · intro h
      exact hjflag.isBigO.trans (hkflag.theta h).2

theorem compare_wForce_row_valid (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) :
    (compareForceRow l.diagramCode.2 l.diagramCode.1
      (fun a b => B (zwOrderSlot 1 a b)) (fun a b => B (zwOrderSlot 0 a b)) D i j k).Valid
      (fun t => (q t).wForce i j) (fun t => (q t).wForce i k) := by
  let p := ZWSystem.pairEstimateData q hb i j hij
  let r := ZWSystem.pairEstimateData q hb i k hik
  have hz := o.compare_z_row_valid B hB i j k
  have hw := o.compare_w_row_valid B hB i j k
  simp only [ZWSystem.zOrderValue, if_neg hij, if_neg hik] at hz
  simp only [ZWSystem.wOrderValue, if_neg hij, if_neg hik] at hw
  have hr := o.compare_radius_domains_valid D hD i j i k hij hik
  have hjflag : LeadingOrderFlag (l.diagramCode.1 (upperIndex i j)) p.zForce
      (fun t => (‖(q t).zVector‖ : ℂ)) := by
    simpa only [ZWSystem.zMaxTermValue, if_neg hij] using l.z_maxTerm_leadingFlag i₀ j₀ hij₀ i j
  have hkflag : LeadingOrderFlag (l.diagramCode.1 (upperIndex i k)) r.zForce
      (fun t => (‖(q t).zVector‖ : ℂ)) := by
    simpa only [ZWSystem.zMaxTermValue, if_neg hik] using l.z_maxTerm_leadingFlag i₀ j₀ hij₀ i k
  unfold compareForceRow
  apply OrderComparison.Valid.orElse
  · apply compareLeadingFlags_valid
    · simpa only [ZWSystem.wMaxTermValue, if_neg hij] using l.w_maxTerm_leadingFlag i₀ j₀ hij₀ i j
    · simpa only [ZWSystem.wMaxTermValue, if_neg hik] using l.w_maxTerm_leadingFlag i₀ j₀ hij₀ i k
  · refine p.compare_wForce_algebra_valid r _ _ _ _ _ hz hw hr ?_ ?_
    · intro h
      exact hkflag.isBigO.trans (hjflag.theta h).2
    · intro h
      exact hjflag.isBigO.trans (hkflag.theta h).2

theorem compare_position_zForce_row_valid (i j : Fin n) (hij : i ≠ j) :
    (comparePositionForceRow l.diagramCode.1 (fun a b => B (zwOrderSlot 0 a b)) D i j).Valid
      (fun t => (q t).z i) (fun t => (q t).zForce i j) := by
  let p := ZWSystem.pairEstimateData q hb i j hij
  have hx := o.compare_z_row_valid B hB i i j
  simp only [ZWSystem.zOrderValue, if_neg hij] at hx
  have hr := o.compare_one_to_radius_valid D hD i j hij
  unfold comparePositionForceRow
  apply OrderComparison.Valid.orElse
  · apply compareLeadingFlags_valid
    · simpa only [ZWSystem.zMaxTermValue, if_pos rfl] using l.z_maxTerm_leadingFlag i₀ j₀ hij₀ i i
    · simpa only [ZWSystem.zMaxTermValue, if_neg hij] using l.z_maxTerm_leadingFlag i₀ j₀ hij₀ i j
  · exact p.compare_position_zForce_algebra_valid _ _ hx hr

theorem compare_position_wForce_row_valid (i j : Fin n) (hij : i ≠ j) :
    (comparePositionForceRow l.diagramCode.2 (fun a b => B (zwOrderSlot 1 a b)) D i j).Valid
      (fun t => (q t).w i) (fun t => (q t).wForce i j) := by
  let p := ZWSystem.pairEstimateData q hb i j hij
  have hx := o.compare_w_row_valid B hB i i j
  simp only [ZWSystem.wOrderValue, if_neg hij] at hx
  have hr := o.compare_one_to_radius_valid D hD i j hij
  unfold comparePositionForceRow
  apply OrderComparison.Valid.orElse
  · apply compareLeadingFlags_valid
    · simpa only [ZWSystem.wMaxTermValue, if_pos rfl] using l.w_maxTerm_leadingFlag i₀ j₀ hij₀ i i
    · simpa only [ZWSystem.wMaxTermValue, if_neg hij] using l.w_maxTerm_leadingFlag i₀ j₀ hij₀ i j
  · exact p.compare_position_wForce_algebra_valid _ _ hx hr

end SequenceOrderAssignment
end CentralConfigurations
