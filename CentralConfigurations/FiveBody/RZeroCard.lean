import CentralConfigurations.FiveBody.SevenTripleCertificate

/-! Universal bound for the complete labelled mass-only list, with no
generic-mass restriction. Sorting is an internal proof device only. -/

namespace CentralConfigurations.FiveBody.RZero
noncomputable section

def relabelTriple (e : Equiv.Perm (Fin 5)) (s : LabelledTriple) : LabelledTriple :=
  ⟨s.val.image e, by simpa only [Finset.card_image_of_injective _ e.injective] using s.prop⟩

theorem additive_relabel_iff (x : Fin 5 → ℝ) (e : Equiv.Perm (Fin 5))
    (s : Finset (Fin 5)) :
    IsAdditiveTriple (x ∘ e) s ↔ IsAdditiveTriple x (s.image e) := by
  constructor
  · rintro ⟨i,j,k,hij,hik,hjk,hs,hx⟩
    refine ⟨e i, e j, e k, e.injective.ne hij, e.injective.ne hik,
      e.injective.ne hjk, ?_, hx⟩
    simp [hs]
  · rintro ⟨i,j,k,hij,hik,hjk,hs,hx⟩
    refine ⟨e.symm i, e.symm j, e.symm k, e.symm.injective.ne hij,
      e.symm.injective.ne hik, e.symm.injective.ne hjk, ?_, ?_⟩
    · have hh := congrArg (fun t : Finset (Fin 5) => t.image e.symm) hs
      simpa [Finset.image_image] using hh
    · simpa using hx

theorem additive_card_relabel (x : Fin 5 → ℝ) (e : Equiv.Perm (Fin 5)) :
    (additiveTriples (x ∘ e)).card = (additiveTriples x).card := by
  apply Finset.card_bij (fun s _ => relabelTriple e s)
  · intro s hs
    exact (mem_additiveTriples _ _).mpr
      ((additive_relabel_iff x e s.val).mp ((mem_additiveTriples _ _).mp hs))
  · intro s hs t ht hst
    apply Subtype.ext
    have hh := congrArg (fun u : LabelledTriple => u.val.image e.symm) hst
    simpa [relabelTriple, Finset.image_image] using hh
  · intro s hs
    refine ⟨relabelTriple e.symm s, ?_, ?_⟩
    · apply (mem_additiveTriples _ _).mpr
      apply (additive_relabel_iff x e _).mpr
      simpa [relabelTriple, Finset.image_image] using (mem_additiveTriples _ _).mp hs
    · apply Subtype.ext
      simp [relabelTriple, Finset.image_image]

theorem additive_ordered_iff (x : Fin 5 → ℝ) (hx : ∀ i, 0 < x i)
    (hmono : Monotone x) (e : Fin 10) :
    IsAdditiveTriple x (tripleLabels e) ↔ orderedEquation x e := by
  have h01 : complementTriple e 0 ≤ complementTriple e 1 := by
    fin_cases e <;> decide +kernel
  have h12 : complementTriple e 1 ≤ complementTriple e 2 := by
    fin_cases e <;> decide +kernel
  rw [additive_on_triple_iff]
  dsimp [orderedEquation]
  constructor
  · rintro (h | h | h)
    · exfalso
      linarith [hmono h01, hx (complementTriple e 2)]
    · exfalso
      linarith [hmono h12, hx (complementTriple e 0)]
    · exact h
  · exact Or.inr ∘ Or.inr

def orderedAdditiveList (x : Fin 5 → ℝ) : Finset (Fin 10) :=
  by classical exact Finset.univ.filter (orderedEquation x)

theorem additive_card_eq_ordered (x : Fin 5 → ℝ) (hx : ∀ i, 0 < x i)
    (hmono : Monotone x) :
    (additiveTriples x).card = (orderedAdditiveList x).card := by
  classical
  apply Finset.card_bij (fun s _ => tripleEquiv.symm s)
  · intro s hs
    simp only [orderedAdditiveList, Finset.mem_filter, Finset.mem_univ, true_and]
    apply (additive_ordered_iff x hx hmono _).mp
    have he := congrArg Subtype.val (tripleEquiv.apply_symm_apply s)
    change tripleLabels (tripleEquiv.symm s) = s.val at he
    rw [he]
    exact (mem_additiveTriples _ _).mp hs
  · intro a ha b hb hab
    exact tripleEquiv.symm.injective hab
  · intro e he
    refine ⟨tripleEquiv e, ?_, tripleEquiv.symm_apply_apply e⟩
    apply (mem_additiveTriples _ _).mpr
    apply (additive_ordered_iff x hx hmono e).mpr
    simpa [orderedAdditiveList] using he

theorem orderedAdditiveList_card_le_six (x : Fin 5 → ℝ) (hx : 0 < x 0) :
    (orderedAdditiveList x).card ≤ 6 := by
  classical
  by_contra h
  have hn : 7 ≤ (orderedAdditiveList x).card := by omega
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hn
  have hz := seven_constraints_force_zero x s hcard (fun e he => by
    have hh := hs he
    simpa [orderedAdditiveList] using hh)
  linarith

theorem additiveTriples_card_le_six (x : Fin 5 → ℝ) (hx : ∀ i, 0 < x i) :
    (additiveTriples x).card ≤ 6 := by
  let e := Tuple.sort x
  have hs : Monotone (x ∘ e) := Tuple.monotone_sort x
  rw [← additive_card_relabel x e]
  calc
    (additiveTriples (x ∘ e)).card = (orderedAdditiveList (x ∘ e)).card :=
      additive_card_eq_ordered (x ∘ e) (fun i => hx (e i)) hs
    _ ≤ 6 := orderedAdditiveList_card_le_six _ (hx (e 0))

theorem completeR_card_le_six (mass : Fin 5 → ℝ) (hm : ∀ i, 0 < mass i) :
    (completeR mass).card ≤ 6 := by
  rw [completeR_card_eq_additive mass hm]
  apply additiveTriples_card_le_six
  intro i
  exact inv_pos.mpr (Real.sqrt_pos.mpr (hm i))

theorem sharp_repeated_mass_list :
    completeR ![1,1,1,1,(1/4 : ℝ)] = {0,1,2,4,5,7} := by
  ext e
  fin_cases e <;>
    norm_num [completeR, trianglePolynomial, complementTriple, triangleMassPolynomial,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
      Matrix.vecHead, Matrix.vecTail, Fin.ext_iff]

theorem sharp_repeated_mass_card : (completeR ![1,1,1,1,(1/4 : ℝ)]).card = 6 := by
  rw [sharp_repeated_mass_list]
  decide +kernel

end
end CentralConfigurations.FiveBody.RZero
