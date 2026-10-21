import CentralConfigurations.Enumeration.RemoteBodyOrderDomains

/-!
# Appendix II Prop2, including its zero-maximum branch

The printed Proposition 4.10 gives a weak inequality at level zero, whereas
Appendix II uses a strict inequality there. Under the remote-distance guard,
a zero maximum for all other positions is impossible: the force estimate
would put every position in level zero, contradicting an off-diagonal lower
bound and the position triangle inequality. Thus the extra deletion is sound.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

def appendixRemotePositionAt {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i : Fin n) : OrderBox (ZWOrderIndex n) :=
  if (otherPositionDomain B color i).sup id = 0 then
    Function.update B (zwOrderSlot color i i) ∅
  else remotePositionAt B color i

theorem remote_nonzero_bound_predicate : ∀ k : Fin 6, k ≠ 0 → ∀ a : Fin 6,
    (if k ∈ ({1, 3, 5} : Finset (Fin 6)) then a < k else a ≤ k) ↔
    (if k ∈ ({2, 4} : Finset (Fin 6)) then a ≤ k else a < k) := by decide

/-- Equality with the actual two-way test in Appendix II's Prop2. -/
theorem appendixRemotePositionAt_eq_filter {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i : Fin n) :
    appendixRemotePositionAt B color i =
      Function.update B (zwOrderSlot color i i) ((B (zwOrderSlot color i i)).filter fun a =>
        if (otherPositionDomain B color i).sup id ∈ ({2, 4} : Finset (Fin 6))
        then a ≤ (otherPositionDomain B color i).sup id
        else a < (otherPositionDomain B color i).sup id) := by
  by_cases hzero : (otherPositionDomain B color i).sup id = 0
  · simp [appendixRemotePositionAt, hzero]
  · rw [appendixRemotePositionAt, if_neg hzero, remotePositionAt]
    congr 1
    apply Finset.filter_congr
    intro a _
    exact remote_nonzero_bound_predicate _ hzero a

def appendixRemoteBodyStep {n : ℕ} (B : OrderBox (ZWOrderIndex n)) (i : Fin n) :
    OrderBox (ZWOrderIndex n) :=
  appendixRemotePositionAt (appendixRemotePositionAt B 0 i) 1 i

def appendixRemoteBodyRefine {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n))
    (i : Fin n) : OrderBox (ZWOrderIndex n) :=
  if remoteDistanceCheck d B i then appendixRemoteBodyStep B i else B

def appendixRemoteBodiesSweep {n : ℕ} (d : DiagramCode n) (bodies : List (Fin n))
    (B : OrderBox (ZWOrderIndex n)) : OrderBox (ZWOrderIndex n) :=
  bodies.foldl (appendixRemoteBodyRefine d) B

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem exists_positive_z_position_level : ∃ i, 0 < o.z i i := by
  by_contra hn
  have hz (i : Fin n) : o.z i i = 0 := by
    have hi : ¬ 0 < o.z i i := fun h => hn ⟨i, h⟩
    apply Fin.ext
    omega
  have ht := (o.z_position_triangle i₀ j₀ hij₀).1
  rw [hz i₀, hz j₀, max_self] at ht
  apply o.z_ne_zero hb i₀ j₀ hij₀
  apply Fin.ext
  omega

theorem exists_positive_w_position_level : ∃ i, 0 < o.w i i := by
  by_contra hn
  have hw (i : Fin n) : o.w i i = 0 := by
    have hi : ¬ 0 < o.w i i := fun h => hn ⟨i, h⟩
    apply Fin.ext
    omega
  have ht := (o.w_position_triangle i₀ j₀ hij₀).1
  rw [hw i₀, hw j₀, max_self] at ht
  apply o.w_ne_zero hb i₀ j₀ hij₀
  apply Fin.ext
  omega

theorem remote_other_position_domain_sup_ne_zero (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color : Fin 2) (i : Fin n)
    (hr : ∀ j, j ≠ i → 3 < o.radius i j) : (otherPositionDomain B color i).sup id ≠ 0 := by
  intro hzero
  fin_cases color
  · change (otherPositionDomain B 0 i).sup id = 0 at hzero
    have hother : ∀ j, j ≠ i → o.z j j ≤ (0 : Fin 6) := by
      intro j hji
      simpa only [hzero, orderCode_z] using o.other_position_le_domain_sup B hB 0 i j hji
    have hi := (o.remote_z_level_bound i hr 0 hother).1
    obtain ⟨j, hj⟩ := o.exists_positive_z_position_level hb
    by_cases hji : j = i
    · subst j; exact (not_le_of_gt hj) hi
    · exact (not_le_of_gt hj) (hother j hji)
  · change (otherPositionDomain B 1 i).sup id = 0 at hzero
    have hother : ∀ j, j ≠ i → o.w j j ≤ (0 : Fin 6) := by
      intro j hji
      simpa only [hzero, orderCode_w] using o.other_position_le_domain_sup B hB 1 i j hji
    have hi := (o.remote_w_level_bound i hr 0 hother).1
    obtain ⟨j, hj⟩ := o.exists_positive_w_position_level hb
    by_cases hji : j = i
    · subst j; exact (not_le_of_gt hj) hi
    · exact (not_le_of_gt hj) (hother j hji)

theorem admitted_appendixRemotePositionAt (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color : Fin 2) (i : Fin n)
    (hr : ∀ j, j ≠ i → 3 < o.radius i j) :
    (appendixRemotePositionAt B color i).Admits o.orderCode := by
  rw [appendixRemotePositionAt, if_neg (o.remote_other_position_domain_sup_ne_zero hb B hB color i hr)]
  exact o.admitted_remotePositionAt B hB color i hr

theorem admitted_appendixRemoteBodyStep (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (i : Fin n)
    (hr : ∀ j, j ≠ i → 3 < o.radius i j) :
    (appendixRemoteBodyStep B i).Admits o.orderCode := by
  have h₁ := o.admitted_appendixRemotePositionAt hb B hB 0 i hr
  exact o.admitted_appendixRemotePositionAt hb _ h₁ 1 i hr

variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))

theorem admitted_appendixRemoteBodyRefine (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (i : Fin n) :
    (appendixRemoteBodyRefine l.diagramCode B i).Admits o.orderCode := by
  unfold appendixRemoteBodyRefine
  split_ifs with hcheck
  · exact o.admitted_appendixRemoteBodyStep hb B hB i
      (o.radius_gt_three_of_remoteDistanceCheck l hb B hB i hcheck)
  · exact hB

theorem admitted_appendixRemoteBodiesSweep (bodies : List (Fin n))
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    (appendixRemoteBodiesSweep l.diagramCode bodies B).Admits o.orderCode := by
  induction bodies generalizing B with
  | nil => exact hB
  | cons i bodies ih => exact ih _ (o.admitted_appendixRemoteBodyRefine hb l B hB i)

end SequenceOrderAssignment

theorem ZWOrderCoverage.appendixRemoteBodiesSweep {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (bodies : List (Fin n)) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (C.image (appendixRemoteBodiesSweep l.diagramCode bodies)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_appendixRemoteBodiesSweep (fun t => hb (φ t))
      (l.comp φ hφ.tendsto_atTop) bodies B ho⟩

end CentralConfigurations
