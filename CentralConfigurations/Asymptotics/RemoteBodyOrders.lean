import CentralConfigurations.Asymptotics.SequenceOrders

/-!
# Remote-body force bounds for Proposition 4.10

When all inverse distances from a body tend to zero, that body's nonzero
position cannot dominate every other position. The finite-sum force proof
gives exactly the weak bound for open levels and strict bound for precise
levels needed in Proposition 4.10. No unproved Proposition 2.8 is assumed.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter Asymptotics

theorem HasOrderLevel.isBigO_of_le_precise {s : OrderScales} {f g : ℕ → ℂ}
    {k l : Fin 6} (hf : HasOrderLevel s f k) (hg : HasOrderLevel s g l)
    (hlk : l ≤ k) (hk : k ∈ ({1, 3, 5} : Finset (Fin 6))) : g =O[atTop] f := by
  rcases lt_or_eq_of_le hlk with hlt | rfl
  · exact (hg.littleO_of_lt hf hlt).isBigO
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact hg.1.trans hf.2
    · exact hg.1.trans hf.2
    · exact hg.1.trans hf.2

theorem ZWSystem.remote_z_not_dominant {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i : Fin n)
    (hd : ∀ j, j ≠ i → (fun t => (q t).delta i j) =o[atTop] (fun _ => (1 : ℂ)))
    (hg : ∀ j, j ≠ i → (fun t => (q t).z j) =O[atTop] (fun t => (q t).z i))
    (hn : ∀ᶠ t in atTop, (q t).z i ≠ 0) : False := by
  have hterm (j : Fin n) :
      (fun t => mass j * (q t).delta i j ^ 3 * ((q t).z i - (q t).z j)) =o[atTop]
        (fun t => (q t).z i) := by
    by_cases hji : j = i
    · simp only [hji, sub_self, mul_zero]
      exact isLittleO_zero _ _
    · have hc : (fun t => mass j * (q t).delta i j ^ 3) =o[atTop] (fun _ => (1 : ℂ)) := by
        simpa only [one_pow] using ((hd j hji).pow (by decide : 0 < 3)).const_mul_left (mass j)
      have hsub := (isBigO_refl (fun t => (q t).z i) atTop).sub (hg j hji)
      simpa only [one_mul] using hc.mul_isBigO hsub
  have hsum : (fun t => ∑ j, mass j * (q t).delta i j ^ 3 * ((q t).z i - (q t).z j))
      =o[atTop] (fun t => (q t).z i) := IsLittleO.sum (fun j _ => hterm j)
  exact isLittleO_irrefl hn.frequently
    (hsum.congr (fun t => ((q t).force_z i).symm) (fun _ => rfl))

theorem ZWSystem.remote_w_not_dominant {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i : Fin n)
    (hd : ∀ j, j ≠ i → (fun t => (q t).delta i j) =o[atTop] (fun _ => (1 : ℂ)))
    (hg : ∀ j, j ≠ i → (fun t => (q t).w j) =O[atTop] (fun t => (q t).w i))
    (hn : ∀ᶠ t in atTop, (q t).w i ≠ 0) : False :=
  ZWSystem.remote_z_not_dominant (fun t => (q t).swap) i hd hg hn

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

theorem delta_littleO_one_of_radius_gt_three (i j : Fin n) (hr : 3 < o.radius i j) :
    (fun t => (q t).delta i j) =o[atTop] (fun _ => (1 : ℂ)) := by
  have hh : (fun _ : ℕ => (1 : ℂ)) =o[atTop] (fun t => ((q t).delta i j)⁻¹) :=
    (o.radius_level i j).middle_littleO_of_three_lt hr
  have h := hh.inv_rev (Eventually.of_forall fun _ h => (one_ne_zero h).elim)
  simpa only [inv_inv, inv_one] using h

theorem remote_z_level_bound (i : Fin n)
    (hr : ∀ j, j ≠ i → 3 < o.radius i j) (k : Fin 6)
    (hk : ∀ j, j ≠ i → o.z j j ≤ k) :
    o.z i i ≤ k ∧ (k ∈ ({1, 3, 5} : Finset (Fin 6)) → o.z i i < k) := by
  have hd := fun j hji => o.delta_littleO_one_of_radius_gt_three i j (hr j hji)
  have hle : o.z i i ≤ k := by
    by_contra hn
    have hlt := lt_of_not_ge hn
    apply ZWSystem.remote_z_not_dominant q i hd
    · intro j hji
      exact ((o.z_position_level j).littleO_of_lt (o.z_position_level i)
        ((hk j hji).trans_lt hlt)).isBigO
    · exact (o.z_position_level i).eventually_nonzero (by omega)
  refine ⟨hle, ?_⟩
  intro hprecise
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    apply ZWSystem.remote_z_not_dominant q i hd
    · intro j hji
      apply (o.z_position_level i).isBigO_of_le_precise (o.z_position_level j)
      · simpa only [heq] using hk j hji
      · simpa only [heq] using hprecise
    · apply (o.z_position_level i).eventually_nonzero
      simp only [Finset.mem_insert, Finset.mem_singleton] at hprecise
      omega

theorem remote_w_level_bound (i : Fin n)
    (hr : ∀ j, j ≠ i → 3 < o.radius i j) (k : Fin 6)
    (hk : ∀ j, j ≠ i → o.w j j ≤ k) :
    o.w i i ≤ k ∧ (k ∈ ({1, 3, 5} : Finset (Fin 6)) → o.w i i < k) := by
  have hd := fun j hji => o.delta_littleO_one_of_radius_gt_three i j (hr j hji)
  have hle : o.w i i ≤ k := by
    by_contra hn
    have hlt := lt_of_not_ge hn
    apply ZWSystem.remote_w_not_dominant q i hd
    · intro j hji
      exact ((o.w_position_level j).littleO_of_lt (o.w_position_level i)
        ((hk j hji).trans_lt hlt)).isBigO
    · exact (o.w_position_level i).eventually_nonzero (by omega)
  refine ⟨hle, ?_⟩
  intro hprecise
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    apply ZWSystem.remote_w_not_dominant q i hd
    · intro j hji
      apply (o.w_position_level i).isBigO_of_le_precise (o.w_position_level j)
      · simpa only [heq] using hk j hji
      · simpa only [heq] using hprecise
    · apply (o.w_position_level i).eventually_nonzero
      simp only [Finset.mem_insert, Finset.mem_singleton] at hprecise
      omega

end SequenceOrderAssignment

end CentralConfigurations
