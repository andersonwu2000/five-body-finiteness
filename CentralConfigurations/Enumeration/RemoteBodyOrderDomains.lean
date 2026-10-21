import CentralConfigurations.Asymptotics.RemoteBodyOrders
import CentralConfigurations.Enumeration.DistanceOrderDomains

/-!
# Proposition 4.10: executable remote-body updates

The guard checks every distance domain from the selected body, including
both levels 4 and 5. At an odd, precise upper level the position bound is
strict; at an even, open level it is weak. The two colors are updated in
sequence, and later body updates recompute their distance-domain guard.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

def otherPositionDomain {n : ℕ} (B : OrderBox (ZWOrderIndex n)) (color : Fin 2) (i : Fin n) :
    Finset (Fin 6) :=
  (Finset.univ.erase i).biUnion fun j => B (zwOrderSlot color j j)

def remotePositionAt {n : ℕ} (B : OrderBox (ZWOrderIndex n)) (color : Fin 2) (i : Fin n) :
    OrderBox (ZWOrderIndex n) :=
  let bound := (otherPositionDomain B color i).sup id
  Function.update B (zwOrderSlot color i i)
    ((B (zwOrderSlot color i i)).filter fun a =>
      if bound ∈ ({1, 3, 5} : Finset (Fin 6)) then a < bound else a ≤ bound)

def remoteBodyStep {n : ℕ} (B : OrderBox (ZWOrderIndex n)) (i : Fin n) :
    OrderBox (ZWOrderIndex n) := remotePositionAt (remotePositionAt B 0 i) 1 i

def remoteDistanceCheck {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n))
    (i : Fin n) : Bool :=
  decide (∀ j : Fin n, j ≠ i →
    radiusDomainEntry (producedDistanceBox d B) i j ⊆ ({4, 5} : Finset (Fin 6)))

def remoteBodyRefine {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n))
    (i : Fin n) : OrderBox (ZWOrderIndex n) :=
  if remoteDistanceCheck d B i then remoteBodyStep B i else B

def remoteBodiesSweep {n : ℕ} (d : DiagramCode n) (bodies : List (Fin n))
    (B : OrderBox (ZWOrderIndex n)) : OrderBox (ZWOrderIndex n) :=
  bodies.foldl (remoteBodyRefine d) B

theorem remotePositionAt_refines {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i : Fin n) : (remotePositionAt B color i).Refines B := by
  intro p
  by_cases hp : p = zwOrderSlot color i i
  · subst p
    simpa only [remotePositionAt, Function.update_self] using
      (Finset.filter_subset (fun a =>
        if (otherPositionDomain B color i).sup id ∈ ({1, 3, 5} : Finset (Fin 6))
        then a < (otherPositionDomain B color i).sup id
        else a ≤ (otherPositionDomain B color i).sup id) (B (zwOrderSlot color i i)))
  · simp only [remotePositionAt, Function.update_of_ne hp]
    exact Finset.Subset.refl _

theorem remoteBodyRefine_refines {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n))
    (i : Fin n) : (remoteBodyRefine d B i).Refines B := by
  unfold remoteBodyRefine
  split_ifs
  · intro p
    exact (remotePositionAt_refines (remotePositionAt B 0 i) 1 i p).trans
      (remotePositionAt_refines B 0 i p)
  · exact fun _ => Finset.Subset.refl _

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

theorem other_position_le_domain_sup (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color : Fin 2) (i j : Fin n) (hji : j ≠ i) :
    o.orderCode (zwOrderSlot color j j) ≤ (otherPositionDomain B color i).sup id :=
  Finset.le_sup (f := id) (Finset.mem_biUnion.mpr
    ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, hB _⟩)

theorem admitted_remotePositionAt (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color : Fin 2) (i : Fin n)
    (hr : ∀ j, j ≠ i → 3 < o.radius i j) :
    (remotePositionAt B color i).Admits o.orderCode := by
  have hk : o.orderCode (zwOrderSlot color i i) ≤ (otherPositionDomain B color i).sup id ∧
      ((otherPositionDomain B color i).sup id ∈ ({1, 3, 5} : Finset (Fin 6)) →
        o.orderCode (zwOrderSlot color i i) < (otherPositionDomain B color i).sup id) := by
    fin_cases color
    · change o.orderCode (zwOrderSlot 0 i i) ≤ (otherPositionDomain B 0 i).sup id ∧
        ((otherPositionDomain B 0 i).sup id ∈ ({1, 3, 5} : Finset (Fin 6)) →
          o.orderCode (zwOrderSlot 0 i i) < (otherPositionDomain B 0 i).sup id)
      simpa only [orderCode_z] using o.remote_z_level_bound i hr
        ((otherPositionDomain B 0 i).sup id) (fun j hji => by
          simpa only [orderCode_z] using o.other_position_le_domain_sup B hB 0 i j hji)
    · change o.orderCode (zwOrderSlot 1 i i) ≤ (otherPositionDomain B 1 i).sup id ∧
        ((otherPositionDomain B 1 i).sup id ∈ ({1, 3, 5} : Finset (Fin 6)) →
          o.orderCode (zwOrderSlot 1 i i) < (otherPositionDomain B 1 i).sup id)
      simpa only [orderCode_w] using o.remote_w_level_bound i hr
        ((otherPositionDomain B 1 i).sup id) (fun j hji => by
          simpa only [orderCode_w] using o.other_position_le_domain_sup B hB 1 i j hji)
  apply hB.update_of_mem
  apply Finset.mem_filter.mpr
  refine ⟨hB _, ?_⟩
  split_ifs with hprecise
  · exact hk.2 hprecise
  · exact hk.1

theorem admitted_remoteBodyStep (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (i : Fin n)
    (hr : ∀ j, j ≠ i → 3 < o.radius i j) :
    (remoteBodyStep B i).Admits o.orderCode := by
  have h₁ := o.admitted_remotePositionAt B hB 0 i hr
  exact o.admitted_remotePositionAt _ h₁ 1 i hr

variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem radius_gt_three_of_remoteDistanceCheck (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (i : Fin n) (hcheck : remoteDistanceCheck l.diagramCode B i = true) :
    ∀ j, j ≠ i → 3 < o.radius i j := by
  intro j hji
  have hc := of_decide_eq_true hcheck
  have hd := o.admitted_producedDistanceBox l hb B hB
  have hm := hc j hji (o.admitted_radiusMatrix _ hd i j hji.symm)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  omega

theorem admitted_remoteBodyRefine (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (i : Fin n) :
    (remoteBodyRefine l.diagramCode B i).Admits o.orderCode := by
  unfold remoteBodyRefine
  split_ifs with hcheck
  · exact o.admitted_remoteBodyStep B hB i (o.radius_gt_three_of_remoteDistanceCheck l hb B hB i hcheck)
  · exact hB

theorem admitted_remoteBodiesSweep (bodies : List (Fin n))
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    (remoteBodiesSweep l.diagramCode bodies B).Admits o.orderCode := by
  induction bodies generalizing B with
  | nil => exact hB
  | cons i bodies ih => exact ih _ (o.admitted_remoteBodyRefine l hb B hB i)

end SequenceOrderAssignment

theorem ZWOrderCoverage.remoteBodiesSweep {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (bodies : List (Fin n)) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (C.image (remoteBodiesSweep l.diagramCode bodies)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_remoteBodiesSweep (l.comp φ hφ.tendsto_atTop) (fun t => hb (φ t)) bodies B ho⟩

end CentralConfigurations
