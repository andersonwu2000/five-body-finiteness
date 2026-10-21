import CentralConfigurations.Asymptotics.ClusterOrigin
import CentralConfigurations.Asymptotics.RemoteBodyOrders
import CentralConfigurations.Enumeration.CenterOfMassOrders

/-!
# Proposition 4.9: close-pair domain updates

The opposite-color row has one precise level. The chosen separation has
strictly lower levels than every other same-color separation in its row.
Proposition 2.7 then bounds both endpoint positions by that separation.
The three sequential filters, their guarded versions, and finite sweeps
preserve coverage of every actual order assignment and every subsequence.
-/

namespace CentralConfigurations

open scoped Topology BigOperators
open Filter Asymptotics

theorem HasOrderLevel.isTheta_of_eq_precise {s : OrderScales} {f g : ℕ → ℂ}
    {k l : Fin 6} (hf : HasOrderLevel s f k) (hg : HasOrderLevel s g l)
    (heq : k = l) (hk : k ∈ ({1, 3, 5} : Finset (Fin 6))) : f =Θ[atTop] g := by
  subst l
  exact ⟨hg.isBigO_of_le_precise hf le_rfl hk, hf.isBigO_of_le_precise hg le_rfl hk⟩

def closePairCheck {n : ℕ} (B : OrderBox (ZWOrderIndex n)) (color other : Fin 2)
    (i j : Fin n) : Bool :=
  decide (i ≠ j ∧ color ≠ other ∧
    (∃ a ∈ ({1, 3, 5} : Finset (Fin 6)), rowOrderDomain B other i = {a}) ∧
    ∀ k : Fin n, k ≠ i → k ≠ j →
      ∀ a ∈ B (zwOrderSlot color i k), (B (zwOrderSlot color i j)).sup id < a)

def closePairPositions {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i j : Fin n) : OrderBox (ZWOrderIndex n) :=
  let bound := (B (zwOrderSlot color i j)).sup id
  let Bi := Function.update B (zwOrderSlot color i i)
    ((B (zwOrderSlot color i i)).filter fun a => a ≤ bound)
  Function.update Bi (zwOrderSlot color j j)
    ((Bi (zwOrderSlot color j j)).filter fun a => a ≤ bound)

def closePairStep {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i j : Fin n) : OrderBox (ZWOrderIndex n) :=
  let Bp := closePairPositions B color i j
  let bound := (Bp (zwOrderSlot color i i) ∪ Bp (zwOrderSlot color j j)).inf id
  Function.update Bp (zwOrderSlot color i j)
    ((Bp (zwOrderSlot color i j)).filter fun a => bound ≤ a)

def closePairRefine {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color other : Fin 2) (i j : Fin n) : OrderBox (ZWOrderIndex n) :=
  if closePairCheck B color other i j then closePairStep B color i j else B

def closePairsSweep {n : ℕ} (entries : List (Fin 2 × Fin 2 × Fin n × Fin n))
    (B : OrderBox (ZWOrderIndex n)) : OrderBox (ZWOrderIndex n) :=
  entries.foldl (fun B e => closePairRefine B e.1 e.2.1 e.2.2.1 e.2.2.2) B

theorem OrderBox.filter_entry_refines {ι : Type*} [DecidableEq ι]
    (B : OrderBox ι) (i : ι) (p : Fin 6 → Prop) [DecidablePred p] :
    OrderBox.Refines (Function.update B i ((B i).filter p)) B := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using Finset.filter_subset p (B i)
  · simp only [Function.update_of_ne hji]
    exact Finset.Subset.refl _

theorem closePairPositions_refines {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i j : Fin n) : (closePairPositions B color i j).Refines B := by
  intro p
  exact (OrderBox.filter_entry_refines _ _ _ p).trans
    (OrderBox.filter_entry_refines B _ _ p)

theorem closePairStep_refines {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i j : Fin n) : (closePairStep B color i j).Refines B := by
  intro p
  exact (OrderBox.filter_entry_refines _ _ _ p).trans (closePairPositions_refines B color i j p)

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

theorem close_z_pair_level_bounds (i j : Fin n) (hij : i ≠ j)
    (hm : mass j ≠ 0) (hM : (∑ k, mass k) ≠ 0)
    (hz : ∀ k, k ≠ i → k ≠ j → o.z i j < o.z i k)
    (hw : ∃ a ∈ ({1, 3, 5} : Finset (Fin 6)), ∀ k, k ≠ i → o.w i k = a) :
    o.z i i ≤ o.z i j ∧ o.z j j ≤ o.z i j := by
  obtain ⟨a, hap, hwa⟩ := hw
  have hh := ZWSystem.close_pair_contains_origin q i j hij hm hM
    (fun k hki hkj => (o.z_separation_level i j hij).littleO_of_lt
      (o.z_separation_level i k hki.symm) (hz k hki hkj)) (by
      intro k hki _
      apply (o.w_separation_level i j hij).isTheta_of_eq_precise
        (o.w_separation_level i k hki.symm)
      · rw [hwa j hij.symm, hwa k hki]
      · rw [hwa j hij.symm]
        exact hap)
  exact ⟨(o.z_position_level i).le_of_isBigO (o.z_separation_level i j hij) hh.1,
    (o.z_position_level j).le_of_isBigO (o.z_separation_level i j hij) hh.2⟩

theorem close_w_pair_level_bounds (i j : Fin n) (hij : i ≠ j)
    (hm : mass j ≠ 0) (hM : (∑ k, mass k) ≠ 0)
    (hw : ∀ k, k ≠ i → k ≠ j → o.w i j < o.w i k)
    (hz : ∃ a ∈ ({1, 3, 5} : Finset (Fin 6)), ∀ k, k ≠ i → o.z i k = a) :
    o.w i i ≤ o.w i j ∧ o.w j j ≤ o.w i j := by
  obtain ⟨a, hap, hza⟩ := hz
  have hh := ZWSystem.close_w_pair_contains_origin q i j hij hm hM
    (fun k hki hkj => (o.w_separation_level i j hij).littleO_of_lt
      (o.w_separation_level i k hki.symm) (hw k hki hkj)) (by
      intro k hki _
      apply (o.z_separation_level i j hij).isTheta_of_eq_precise
        (o.z_separation_level i k hki.symm)
      · rw [hza j hij.symm, hza k hki]
      · rw [hza j hij.symm]
        exact hap)
  exact ⟨(o.w_position_level i).le_of_isBigO (o.w_separation_level i j hij) hh.1,
    (o.w_position_level j).le_of_isBigO (o.w_separation_level i j hij) hh.2⟩

theorem close_pair_bounds_of_check (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color other : Fin 2) (i j : Fin n)
    (hm : mass j ≠ 0) (hM : (∑ k, mass k) ≠ 0)
    (hcheck : closePairCheck B color other i j = true) :
    o.orderCode (zwOrderSlot color i i) ≤ o.orderCode (zwOrderSlot color i j) ∧
    o.orderCode (zwOrderSlot color j j) ≤ o.orderCode (zwOrderSlot color i j) := by
  obtain ⟨hij, hcolors, ⟨a, hap, hrow⟩, hsmall⟩ := of_decide_eq_true hcheck
  have hr (k : Fin n) (hki : k ≠ i) : o.orderCode (zwOrderSlot other i k) = a := by
    have hk : o.orderCode (zwOrderSlot other i k) ∈ rowOrderDomain B other i :=
      Finset.mem_biUnion.mpr ⟨k, Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩, hB _⟩
    rw [hrow] at hk
    exact Finset.mem_singleton.mp hk
  have hs (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) :
      o.orderCode (zwOrderSlot color i j) < o.orderCode (zwOrderSlot color i k) :=
    (Finset.le_sup (f := id) (hB _)).trans_lt (hsmall k hki hkj _ (hB _))
  fin_cases color <;> fin_cases other
  · exact (hcolors rfl).elim
  · change o.orderCode (zwOrderSlot 0 i i) ≤ o.orderCode (zwOrderSlot 0 i j) ∧
      o.orderCode (zwOrderSlot 0 j j) ≤ o.orderCode (zwOrderSlot 0 i j)
    simpa only [orderCode_z] using o.close_z_pair_level_bounds i j hij hm hM
      (fun k hki hkj => by
        have h := hs k hki hkj
        change o.orderCode (zwOrderSlot 0 i j) < o.orderCode (zwOrderSlot 0 i k) at h
        simpa only [orderCode_z] using h)
      ⟨a, hap, fun k hki => by
        have h := hr k hki
        change o.orderCode (zwOrderSlot 1 i k) = a at h
        simpa only [orderCode_w] using h⟩
  · change o.orderCode (zwOrderSlot 1 i i) ≤ o.orderCode (zwOrderSlot 1 i j) ∧
      o.orderCode (zwOrderSlot 1 j j) ≤ o.orderCode (zwOrderSlot 1 i j)
    simpa only [orderCode_w] using o.close_w_pair_level_bounds i j hij hm hM
      (fun k hki hkj => by
        have h := hs k hki hkj
        change o.orderCode (zwOrderSlot 1 i j) < o.orderCode (zwOrderSlot 1 i k) at h
        simpa only [orderCode_w] using h)
      ⟨a, hap, fun k hki => by
        have h := hr k hki
        change o.orderCode (zwOrderSlot 0 i k) = a at h
        simpa only [orderCode_z] using h⟩
  · exact (hcolors rfl).elim

theorem admitted_closePairPositions (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color : Fin 2) (i j : Fin n)
    (hi : o.orderCode (zwOrderSlot color i i) ≤ o.orderCode (zwOrderSlot color i j))
    (hj : o.orderCode (zwOrderSlot color j j) ≤ o.orderCode (zwOrderSlot color i j)) :
    (closePairPositions B color i j).Admits o.orderCode := by
  have hmax : o.orderCode (zwOrderSlot color i j) ≤ (B (zwOrderSlot color i j)).sup id :=
    Finset.le_sup (f := id) (hB _)
  have hi' := hB.update_of_mem (zwOrderSlot color i i)
    ((B (zwOrderSlot color i i)).filter fun a => a ≤ (B (zwOrderSlot color i j)).sup id)
    (Finset.mem_filter.mpr ⟨hB _, hi.trans hmax⟩)
  exact hi'.update_of_mem _ _ (Finset.mem_filter.mpr ⟨hi' _, hj.trans hmax⟩)

theorem admitted_closePairStep (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color : Fin 2) (i j : Fin n)
    (hi : o.orderCode (zwOrderSlot color i i) ≤ o.orderCode (zwOrderSlot color i j))
    (hj : o.orderCode (zwOrderSlot color j j) ≤ o.orderCode (zwOrderSlot color i j)) :
    (closePairStep B color i j).Admits o.orderCode := by
  have hp := o.admitted_closePairPositions B hB color i j hi hj
  apply hp.update_of_mem
  refine Finset.mem_filter.mpr ⟨hp _, ?_⟩
  exact (Finset.inf_le (f := id) (Finset.mem_union_left _ (hp (zwOrderSlot color i i)))).trans hi

theorem admitted_closePairRefine (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) (color other : Fin 2) (i j : Fin n)
    (hm : mass j ≠ 0) (hM : (∑ k, mass k) ≠ 0) :
    (closePairRefine B color other i j).Admits o.orderCode := by
  unfold closePairRefine
  split_ifs with hc
  · obtain ⟨hi, hj⟩ := o.close_pair_bounds_of_check B hB color other i j hm hM hc
    exact o.admitted_closePairStep B hB color i j hi hj
  · exact hB

theorem admitted_closePairsSweep (entries : List (Fin 2 × Fin 2 × Fin n × Fin n))
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode)
    (hm : ∀ j, mass j ≠ 0) (hM : (∑ k, mass k) ≠ 0) :
    (closePairsSweep entries B).Admits o.orderCode := by
  induction entries generalizing B with
  | nil => exact hB
  | cons e entries ih =>
    exact ih _ (o.admitted_closePairRefine B hB e.1 e.2.1 e.2.2.1 e.2.2.2 (hm _) hM)

end SequenceOrderAssignment

theorem ZWOrderCoverage.closePairsSweep {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (entries : List (Fin 2 × Fin 2 × Fin n × Fin n))
    (hm : ∀ j, mass j ≠ 0) (hM : (∑ k, mass k) ≠ 0) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (C.image (closePairsSweep entries)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_closePairsSweep entries B ho hm hM⟩

end CentralConfigurations
