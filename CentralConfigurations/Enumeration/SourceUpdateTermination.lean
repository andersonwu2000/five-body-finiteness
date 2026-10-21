import CentralConfigurations.Enumeration.OrderDomainTermination
import CentralConfigurations.Enumeration.SourceOrderRefinement

/-! Section 7 update sweeps and their product-count fixed points.
Maximal-edge initialization is deliberately outside the contracting loop:
its source operation writes singletons and need not refine arbitrary boxes.
The update list may use every subsequently proved refinement principle. -/

namespace CentralConfigurations
open scoped Topology
open Filter

namespace OrderBox

theorem exactTriangleAt_refines {ι : Type*} [DecidableEq ι]
    (B : OrderBox ι) (x y z : ι) : (exactTriangleAt B x y z).Refines B :=
  filter_entry_refines B x _

theorem exactTriangleStep_refines {ι : Type*} [DecidableEq ι]
    (B : OrderBox ι) (x y z : ι) : (exactTriangleStep B x y z).Refines B :=
  (exactTriangleAt_refines _ z x y).trans
    ((exactTriangleAt_refines _ y x z).trans (exactTriangleAt_refines B x y z))

theorem equalizeTriple_refines {ι : Type*} [DecidableEq ι]
    (B : OrderBox ι) (x y z : ι) : (equalizeTriple B x y z).Refines B := by
  intro i a ha
  dsimp [equalizeTriple] at ha
  by_cases hiz : i = z
  · subst i
    simp only [Function.update_self,Finset.mem_inter] at ha
    exact ha.2
  · rw [Function.update_of_ne hiz] at ha
    by_cases hiy : i = y
    · subst i
      simp only [Function.update_self,Finset.mem_inter] at ha
      exact ha.1.2
    · rw [Function.update_of_ne hiy] at ha
      by_cases hix : i = x
      · subst i
        simp only [Function.update_self,Finset.mem_inter] at ha
        exact ha.1.1
      · simpa only [Function.update_of_ne hix] using ha

theorem Refines.foldl {ι α : Type*} (B : OrderBox ι)
    (f : OrderBox ι → α → OrderBox ι) (xs : List α)
    (hf : ∀ a ∈ xs, ∀ A, (f A a).Refines A) : (xs.foldl f B).Refines B := by
  induction xs generalizing B with
  | nil => exact fun _ => Finset.Subset.refl _
  | cons a xs ih =>
    exact (ih (f B a) (fun b hb => hf b (List.mem_cons_of_mem a hb))).trans
      (hf a (by simp) B)

end OrderBox

theorem orderRefinementOp_refines {n : ℕ} (op : OrderRefinementOp n)
    (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n)) : (op.apply d B).Refines B := by
  cases op with
  | position c i j =>
    dsimp only [OrderRefinementOp.apply]
    unfold appendixPositionTriangle
    split_ifs
    · exact OrderBox.exactTriangleStep_refines _ _ _ _
    · exact fun _ => Finset.Subset.refl _
  | separation c i j k =>
    dsimp only [OrderRefinementOp.apply]
    unfold appendixSeparationTriangle
    split_ifs
    · exact OrderBox.exactTriangleStep_refines _ _ _ _
    · exact fun _ => Finset.Subset.refl _
  | equal c i j k =>
    dsimp only [OrderRefinementOp.apply]
    unfold checkedEqualTriangle
    split_ifs
    · exact OrderBox.equalizeTriple_refines _ _ _ _
    · exact fun _ => Finset.Subset.refl _
  | estimate i j =>
    dsimp only [OrderRefinementOp.apply]
    split_ifs
    · exact OrderBox.estimatePairStep_refines _ _ _ _
    · exact fun _ => Finset.Subset.refl _

inductive SourceUpdateOp (n : ℕ) where
  | basic (op : OrderRefinementOp n)
  | center (color : Fin 2) (i : Fin n)
  | close (color other : Fin 2) (i j : Fin n)
  | remote (i : Fin n)
  deriving DecidableEq, Repr

def SourceUpdateOp.toSource {n : ℕ} : SourceUpdateOp n → SourceOrderOp n
  | .basic op => .basic op
  | .center c i => .center c i
  | .close c other i j => .close c other i j
  | .remote i => .remote i

def SourceUpdateOp.apply {n : ℕ} (op : SourceUpdateOp n) (d : DiagramCode n)
    (B : OrderBox (ZWOrderIndex n)) : OrderBox (ZWOrderIndex n) := op.toSource.apply d B

theorem SourceUpdateOp.refines {n : ℕ} (op : SourceUpdateOp n) (d : DiagramCode n)
    (B : OrderBox (ZWOrderIndex n)) : (op.apply d B).Refines B := by
  cases op with
  | basic op => exact orderRefinementOp_refines op d B
  | center c i => exact OrderBox.filter_entry_refines B _ _
  | close c other i j =>
    change (closePairRefine B c other i j).Refines B
    unfold closePairRefine
    split_ifs
    · exact closePairStep_refines B c i j
    · exact fun _ => Finset.Subset.refl _
  | remote i =>
    change (appendixRemoteBodyRefine d B i).Refines B
    unfold appendixRemoteBodyRefine
    split_ifs
    · unfold appendixRemoteBodyStep
      have h (A : OrderBox (ZWOrderIndex n)) (c : Fin 2) :
          (appendixRemotePositionAt A c i).Refines A := by
        rw [appendixRemotePositionAt_eq_filter]
        exact OrderBox.filter_entry_refines A _ _
      exact (h _ 1).trans (h B 0)
    · exact fun _ => Finset.Subset.refl _

def sourceUpdateSweep {n : ℕ} (d : DiagramCode n) (ops : List (SourceUpdateOp n))
    (B : OrderBox (ZWOrderIndex n)) : OrderBox (ZWOrderIndex n) :=
  ops.foldl (fun A op => op.apply d A) B

theorem sourceUpdateSweep_refines {n : ℕ} (d : DiagramCode n)
    (ops : List (SourceUpdateOp n)) (B : OrderBox (ZWOrderIndex n)) :
    (sourceUpdateSweep d ops B).Refines B :=
  OrderBox.Refines.foldl B _ ops (fun op _ A => op.refines d A)

/-- A fixed contracting sweep is fixed by every operation in that sweep,
even without monotonicity of the operations as functions of the input box. -/
theorem sourceUpdateSweep_eq_self_iff {n : ℕ} (d : DiagramCode n)
    (ops : List (SourceUpdateOp n)) (B : OrderBox (ZWOrderIndex n)) :
    sourceUpdateSweep d ops B = B ↔ ∀ op ∈ ops, op.apply d B = B := by
  induction ops generalizing B with
  | nil => simp [sourceUpdateSweep]
  | cons op ops ih =>
    change sourceUpdateSweep d ops (op.apply d B) = B ↔ _
    constructor
    · intro h
      have hr := sourceUpdateSweep_refines d ops (op.apply d B)
      rw [h] at hr
      have ho : op.apply d B = B := funext (fun i => Finset.Subset.antisymm (op.refines d B i) (hr i))
      rw [ho] at h
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ho
      · exact (ih B).mp h a ha
    · intro h
      rw [h op (by simp)]
      exact (ih B).mpr (fun a ha => h a (List.mem_cons_of_mem op ha))

def stabilizedSourceUpdate {n : ℕ} (d : DiagramCode n) (ops : List (SourceUpdateOp n))
    (B : OrderBox (ZWOrderIndex n)) : OrderBox (ZWOrderIndex n) :=
  OrderBox.stabilize (sourceUpdateSweep d ops) (sourceUpdateSweep_refines d ops) B

theorem stabilizedSourceUpdate_refines {n : ℕ} (d : DiagramCode n)
    (ops : List (SourceUpdateOp n)) (B : OrderBox (ZWOrderIndex n)) :
    (stabilizedSourceUpdate d ops B).Refines B :=
  OrderBox.stabilize_refines _ _ B

theorem stabilizedSourceUpdate_terminal {n : ℕ} (d : DiagramCode n)
    (ops : List (SourceUpdateOp n)) (B : OrderBox (ZWOrderIndex n)) :
    OrderBox.completionCount (stabilizedSourceUpdate d ops B) = 0 ∨
      sourceUpdateSweep d ops (stabilizedSourceUpdate d ops B) = stabilizedSourceUpdate d ops B :=
  OrderBox.stabilize_terminal _ _ B

namespace SequenceOrderAssignment
variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass)
include hb hm

theorem admitted_sourceUpdateSweep (ops : List (SourceUpdateOp n))
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    (sourceUpdateSweep l.diagramCode ops B).Admits o.orderCode :=
  hB.foldl _ ops (fun op _ A hA => o.admitted_sourceOrderOp l hb hm op.toSource A hA)

theorem admitted_stabilizedSourceUpdate (ops : List (SourceUpdateOp n))
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    (stabilizedSourceUpdate l.diagramCode ops B).Admits o.orderCode :=
  OrderBox.stabilize_preserves _ _ (fun A => A.Admits o.orderCode)
    (fun A hA => o.admitted_sourceUpdateSweep l hb hm ops A hA) B hB

theorem stabilizedSourceUpdate_fixed (ops : List (SourceUpdateOp n))
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    sourceUpdateSweep l.diagramCode ops (stabilizedSourceUpdate l.diagramCode ops B) =
      stabilizedSourceUpdate l.diagramCode ops B :=
  OrderBox.stabilize_fixed_of_admits _ _ B o.orderCode
    (o.admitted_stabilizedSourceUpdate l hb hm ops B hB)

end SequenceOrderAssignment

theorem ZWOrderCoverage.stabilizedSourceUpdate {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : AdmissibleMasses mass)
    (ops : List (SourceUpdateOp n)) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (C.image (stabilizedSourceUpdate l.diagramCode ops)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B,hB,ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_,Finset.mem_image.mpr ⟨B,hB,rfl⟩,
    o.admitted_stabilizedSourceUpdate (l.comp φ hφ.tendsto_atTop)
      (fun t => hb (φ t)) hm ops B ho⟩

end CentralConfigurations
