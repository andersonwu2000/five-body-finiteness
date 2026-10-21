import CentralConfigurations.Enumeration.SequenceOrderDomains
import CentralConfigurations.Model.ZWMassCenter

/-!
# Proposition 4.7(b): mass-center restrictions on diagonal orders

The rowwise rule from the statement and the weaker global-maximum rule from
Appendix II are both proved. The total mass must be nonzero. Empty domains
are totalized by a bottom supremum; an admitted actual assignment supplies
every membership used in the soundness proof.
-/

namespace CentralConfigurations

open scoped Topology BigOperators
open Filter Asymptotics

theorem HasOrderLevel.le_sup_of_weighted_sum {ι : Type*} [DecidableEq ι]
    {s : OrderScales} {f : ℕ → ℂ} {k : Fin 6} (hf : HasOrderLevel s f k)
    (I : Finset ι) (g : ι → ℕ → ℂ) (levels : ι → Fin 6) (c : ι → ℂ)
    (hg : ∀ i ∈ I, HasOrderLevel s (g i) (levels i))
    (M : ℂ) (hM : M ≠ 0) (heq : ∀ t, M * f t = ∑ i ∈ I, c i * g i t) :
    k ≤ I.sup levels := by
  by_contra hn
  have hlt : I.sup levels < k := lt_of_not_ge hn
  have hsmall (i : ι) (hi : i ∈ I) : (fun t => c i * g i t) =o[atTop] f :=
    ((hg i hi).littleO_of_lt hf ((Finset.le_sup hi).trans_lt hlt)).const_mul_left (c i)
  have hs : (fun t => ∑ i ∈ I, c i * g i t) =o[atTop] f := IsLittleO.sum hsmall
  have hmf : (fun t => M * f t) =o[atTop] f :=
    hs.congr (fun t => (heq t).symm) (fun _ => rfl)
  exact isLittleO_irrefl (hf.eventually_nonzero (by omega)).frequently
    ((isLittleO_const_mul_left_iff hM).mp hmf)

def rowOrderDomain {n : ℕ} (B : OrderBox (ZWOrderIndex n)) (color : Fin 2) (i : Fin n) :
    Finset (Fin 6) :=
  (Finset.univ.erase i).biUnion fun j => B (zwOrderSlot color i j)

def globalSeparationDomain {n : ℕ} (B : OrderBox (ZWOrderIndex n)) (color : Fin 2) :
    Finset (Fin 6) :=
  Finset.univ.biUnion fun p : StrictUpperIndex n => B (zwOrderSlot color p.1.1 p.1.2)

theorem zwOrderSlot_symm {n : ℕ} (color : Fin 2) (i j : Fin n) :
    zwOrderSlot color i j = zwOrderSlot color j i := by
  simp only [zwOrderSlot, upperIndex, min_comm, max_comm]

theorem rowOrderDomain_subset_global {n : ℕ} (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i : Fin n) : rowOrderDomain B color i ⊆ globalSeparationDomain B color := by
  intro a ha
  obtain ⟨j, hj, haj⟩ := Finset.mem_biUnion.mp ha
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  rcases lt_or_gt_of_ne hji with hji | hij
  · exact Finset.mem_biUnion.mpr ⟨⟨(j, i), hji⟩, Finset.mem_univ _,
      by simpa only [zwOrderSlot_symm color i j] using haj⟩
  · exact Finset.mem_biUnion.mpr ⟨⟨(i, j), hij⟩, Finset.mem_univ _, haj⟩

def centerOfMassAt {n : ℕ} (global : Bool) (B : OrderBox (ZWOrderIndex n))
    (color : Fin 2) (i : Fin n) : OrderBox (ZWOrderIndex n) :=
  let D := if global then globalSeparationDomain B color else rowOrderDomain B color i
  Function.update B (zwOrderSlot color i i)
    ((B (zwOrderSlot color i i)).filter fun a => a ≤ D.sup id)

def centerOfMassSweep {n : ℕ} (global : Bool) (entries : List (Fin 2 × Fin n))
    (B : OrderBox (ZWOrderIndex n)) : OrderBox (ZWOrderIndex n) :=
  entries.foldl (fun A p => centerOfMassAt global A p.1 p.2) B

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

theorem z_diagonal_le_row_sup (hm : (∑ j, mass j) ≠ 0) (i : Fin n) :
    o.z i i ≤ (Finset.univ.erase i).sup (fun j => o.z i j) := by
  apply (o.z_position_level i).le_sup_of_weighted_sum (Finset.univ.erase i)
    (fun j t => (q t).z i - (q t).z j) (fun j => o.z i j) mass
    (fun j hj => o.z_separation_level i j (Ne.symm (Finset.mem_erase.mp hj).1))
    (∑ j, mass j) hm
  exact fun t => ((q t).mass_separation_sum_z i).symm

theorem w_diagonal_le_row_sup (hm : (∑ j, mass j) ≠ 0) (i : Fin n) :
    o.w i i ≤ (Finset.univ.erase i).sup (fun j => o.w i j) := by
  apply (o.w_position_level i).le_sup_of_weighted_sum (Finset.univ.erase i)
    (fun j t => (q t).w i - (q t).w j) (fun j => o.w i j) mass
    (fun j hj => o.w_separation_level i j (Ne.symm (Finset.mem_erase.mp hj).1))
    (∑ j, mass j) hm
  exact fun t => ((q t).mass_separation_sum_w i).symm

theorem diagonal_le_row_code_sup (hm : (∑ j, mass j) ≠ 0) (color : Fin 2) (i : Fin n) :
    o.orderCode (zwOrderSlot color i i) ≤
      (Finset.univ.erase i).sup (fun j => o.orderCode (zwOrderSlot color i j)) := by
  fin_cases color
  · change o.orderCode (zwOrderSlot 0 i i) ≤
      (Finset.univ.erase i).sup (fun j => o.orderCode (zwOrderSlot 0 i j))
    simpa only [orderCode_z] using o.z_diagonal_le_row_sup hm i
  · change o.orderCode (zwOrderSlot 1 i i) ≤
      (Finset.univ.erase i).sup (fun j => o.orderCode (zwOrderSlot 1 i j))
    simpa only [orderCode_w] using o.w_diagonal_le_row_sup hm i

theorem diagonal_le_row_domain_sup (hm : (∑ j, mass j) ≠ 0)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) (color : Fin 2) (i : Fin n) :
    o.orderCode (zwOrderSlot color i i) ≤ (rowOrderDomain B color i).sup id := by
  apply (o.diagonal_le_row_code_sup hm color i).trans
  apply Finset.sup_le
  intro j hj
  exact Finset.le_sup (f := id) (Finset.mem_biUnion.mpr ⟨j, hj, hB _⟩)

theorem admitted_centerOfMassAt (hm : (∑ j, mass j) ≠ 0)
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode)
    (global : Bool) (color : Fin 2) (i : Fin n) :
    (centerOfMassAt global B color i).Admits o.orderCode := by
  apply hB.update_of_mem
  apply Finset.mem_filter.mpr
  refine ⟨hB _, ?_⟩
  have hr := o.diagonal_le_row_domain_sup hm B hB color i
  cases global
  · exact hr
  · exact hr.trans (Finset.sup_mono (rowOrderDomain_subset_global B color i))

theorem admitted_centerOfMassSweep (hm : (∑ j, mass j) ≠ 0)
    (global : Bool) (entries : List (Fin 2 × Fin n))
    (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode) :
    (centerOfMassSweep global entries B).Admits o.orderCode := by
  induction entries generalizing B with
  | nil => exact hB
  | cons p entries ih =>
    exact ih _ (o.admitted_centerOfMassAt hm B hB global p.1 p.2)

end SequenceOrderAssignment

theorem ZWOrderCoverage.centerOfMassSweep {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) (hm : (∑ j, mass j) ≠ 0)
    (global : Bool) (entries : List (Fin 2 × Fin n)) :
    ZWOrderCoverage q i₀ j₀ hij₀ ha (C.image (centerOfMassSweep global entries)) := by
  apply (zwOrderCoverage_iff_joint q i₀ j₀ hij₀ ha hb _).mpr
  intro φ hφ o
  obtain ⟨B, hB, ho⟩ := hC φ hφ o.orderCode o.hasZWOrderCode
  exact ⟨_, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_centerOfMassSweep hm global entries B ho⟩

end CentralConfigurations
