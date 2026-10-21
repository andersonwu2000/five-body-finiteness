import CentralConfigurations.FiveBody.D9BothMaximal
import CentralConfigurations.FiveBody.PhysicalPotentialFloor

/-!
# D9 exclusion from the attachment-order alternatives

The input consists of actual solutions and an extracted, relabeled,
possibly color-exchanged attachment-order branch. D9RawExclusion.lean
derives this input from the canonical diagram support.
-/

namespace CentralConfigurations.FiveBody.D9
open Filter
open scoped Topology BigOperators

inductive AttachmentOrders {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass)
  | skew (orders : SkewOrders q)
  | bothMaximal (orders : BothMaximalOrders q)

theorem explicit_pair_mass_sum (m : Fin 5 → ℝ) :
    pairMassSum m = (m 0*m 1+m 0*m 2+m 1*m 2)+
      (m 0+m 1+m 2)*(m 3+m 4)+m 3*m 4 := by
  simp [pairMassSum, Fin.sum_univ_succ]
  ring

theorem explicit_total_mass (m : Fin 5 → ℝ) :
    totalMass m = m 0+m 1+m 2+m 3+m 4 := by
  simp [totalMass, Fin.sum_univ_succ]
  ring

theorem false_of_attachment_orders {m : Fin 5 → ℝ} (hm : ∀ i, 0 < m i)
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))} {I0 : ℝ}
    (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.unorderedPotential = (I0 : ℂ))
    (h : AttachmentOrders q) : False := by
  cases h with
  | skew h =>
    exact h.false_of_constant_potential (by exact_mod_cast ne_of_gt (hm 0))
      (by exact_mod_cast ne_of_gt (hm 3)) (I0 : ℂ) hI
  | bothMaximal h =>
    apply h.false_of_physical_potential hm hphysical.1 _ hI
    simpa only [explicit_pair_mass_sum, explicit_total_mass] using hphysical.2

theorem pair_mass_sum_square_identity (m : Fin 5 → ℝ) :
    2 * pairMassSum m = totalMass m ^ 2 - ∑ i, m i ^ 2 := by
  simp [pairMassSum, totalMass, Fin.sum_univ_succ]
  ring

theorem physical_level_relabel {m : Fin 5 → ℝ} {I0 : ℝ}
    (h : PhysicalPotentialLevel m I0) (e : Fin 5 ≃ Fin 5) :
    PhysicalPotentialLevel (fun i => m (e i)) I0 := by
  have hM : totalMass (fun i => m (e i)) = totalMass m := e.sum_comp m
  have hs : (∑ i, m (e i)^2) = ∑ i, m i^2 := e.sum_comp (fun i => m i^2)
  have hS : pairMassSum (fun i => m (e i)) = pairMassSum m := by
    have h1 := pair_mass_sum_square_identity (fun i => m (e i))
    have h2 := pair_mass_sum_square_identity m
    rw [hM, hs] at h1
    linarith
  exact ⟨h.1, by simpa only [hS, hM] using h.2⟩

noncomputable def inRoles {m : Fin 5 → ℝ} (q : ZWSystem ℂ 5 (fun i => (m i : ℂ)))
    (e : Fin 5 ≃ Fin 5) (swapColors : Bool) :
    ZWSystem ℂ 5 (fun i => (m (e i) : ℂ)) :=
  let r := (q.toNormalized.relabel e).toZW
  if swapColors then r.swap else r

theorem inRoles_potential {m : Fin 5 → ℝ}
    (q : ZWSystem ℂ 5 (fun i => (m i : ℂ))) (e : Fin 5 ≃ Fin 5) (swapColors : Bool) :
    (inRoles q e swapColors).toNormalized.unorderedPotential =
      q.toNormalized.unorderedPotential := by
  cases swapColors <;> simp only [inRoles, Bool.false_eq_true, ↓reduceIte]
  all_goals exact q.toNormalized.relabel_unorderedPotential e

/-- The exact remaining source import.  The same strict subsequence and
permutation act on both colors, positions, masses, and inverse distances. -/
def HasExtractedAttachmentOrders {m : Fin 5 → ℝ}
    (q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))) : Prop :=
  ∃ (φ : ℕ → ℕ) (_ : StrictMono φ) (e : Fin 5 ≃ Fin 5) (swapColors : Bool),
    Nonempty (AttachmentOrders (fun t => inRoles (q (φ t)) e swapColors))

/-- D9 exclusion at the corrected exhaustive order-split boundary.  This
covers all role permutations, both colors, all signed complex sheets, and
both arbitrary skew and both-maximal attachment scales. -/
theorem false_of_extracted_attachment_orders {m : Fin 5 → ℝ} (hm : ∀ i, 0 < m i)
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))} {I0 : ℝ}
    (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.unorderedPotential = (I0 : ℂ))
    (hD9 : HasExtractedAttachmentOrders q) : False := by
  obtain ⟨φ, _, e, swapColors, ⟨h⟩⟩ := hD9
  apply false_of_attachment_orders (fun i => hm (e i)) (physical_level_relabel hphysical e) _ h
  intro t
  rw [inRoles_potential, hI]

end CentralConfigurations.FiveBody.D9
