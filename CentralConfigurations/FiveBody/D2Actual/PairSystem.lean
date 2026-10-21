import CentralConfigurations.FiveBody.D2Actual.CommonExtraction

namespace CentralConfigurations.FiveBody.D2
open Filter
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

theorem five_last_two_w_div {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass)
    (a : ℂ) (p : Fin 2) :
    q.w (Fin.natAdd 3 p)/a =
      (∑ k : Fin 2, mass (Fin.natAdd 3 k)*q.delta (Fin.natAdd 3 p) (Fin.natAdd 3 k)^3*
        (q.w (Fin.natAdd 3 p)/a-q.w (Fin.natAdd 3 k)/a)) +
      ∑ i : Fin 3, mass (i.castLE (by decide))*q.wForce (Fin.natAdd 3 p)
        (i.castLE (by decide))/a := by
  fin_cases p
  · have h := q.force_w 3
    simp [Fin.sum_univ_succ] at h ⊢
    dsimp only [ZWSystem.wForce]
    linear_combination a⁻¹*h
  · have h := q.force_w 4
    simp [Fin.sum_univ_succ] at h ⊢
    dsimp only [ZWSystem.wForce]
    linear_combination a⁻¹*h

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I : ℂ}

/-- The extracted pair is a full two-body ZW system, with the same signed root. -/
noncomputable def ActualLimit.pairSystem (s : ActualLimit m q l I) (hm : ∀ i, 0 < m i) :
    ZWSystem ℂ 2 (fun p => (m (Fin.natAdd 3 p) : ℂ)) := by
  let b : Fin 2 → Fin 5 := Fin.natAdd 3
  let D : Fin 2 → Fin 2 → ℂ := fun p k => if p=k then 0 else s.pairDelta
  have hA : (m 3 : ℂ)+m 4 ≠ 0 := by
    exact_mod_cast ne_of_gt (add_pos (hm 3) (hm 4))
  have hD (p k : Fin 2) : Tendsto
      (fun t => (q (s.subsequence t)).delta (b p) (b k)) atTop (𝓝 (D p k)) := by
    fin_cases p <;> fin_cases k
    · simp only [b, ZWSystem.delta_diagonal, D, if_pos rfl]; exact tendsto_const_nhds
    · exact s.pair_delta_limit
    · change Tendsto (fun t => (q (s.subsequence t)).delta 4 3) atTop (𝓝 s.pairDelta)
      exact s.pair_delta_limit.congr' (Eventually.of_forall fun t =>
        (q (s.subsequence t)).delta_symm 3 4)
    · simp only [b, ZWSystem.delta_diagonal, D, if_pos rfl]; exact tendsto_const_nhds
  have hU (p : Fin 2) : Tendsto
      (fun t => (q (s.subsequence t)).inverseScale*(q (s.subsequence t)).z (b p))
        atTop (𝓝 (s.pairZ p)) := by
    rw [s.pairZ_eq p]
    exact (l.z_position (b p)).comp s.strictMono.tendsto_atTop
  have hforceZ : ∀ p, s.pairZ p = ∑ k : Fin 2,
      (m (b k) : ℂ)*D p k^3*(s.pairZ p-s.pairZ k) := by
    intro p
    fin_cases p <;> simp [Fin.sum_univ_succ, D, b, s.pair_delta_cube]
    · field_simp [hA]
      linear_combination s.pair_balance
    · field_simp [hA]
      linear_combination s.pair_balance
  have hforceW : ∀ p, s.pairW p = ∑ k : Fin 2,
      (m (b k) : ℂ)*D p k^3*(s.pairW p-s.pairW k) := by
    intro p
    have hsum := tendsto_finsetSum Finset.univ (fun k _ =>
      (((hD p k).pow 3).const_mul (m (b k) : ℂ)).mul
        ((s.pair_w_limit p).sub (s.pair_w_limit k)))
    have hcross := tendsto_finsetSum Finset.univ (fun i _ =>
      (s.cross_w_force_limit p i).const_mul (m (i.castLE (by decide)) : ℂ))
    simp only [mul_zero, Finset.sum_const_zero] at hcross
    have htotal := hsum.add hcross
    simp only [add_zero] at htotal
    have heq t := five_last_two_w_div (q (s.subsequence t))
      (q (s.subsequence t)).inverseScale p
    have h := htotal.congr' (Eventually.of_forall fun t => by
      simpa only [b, mul_div_assoc] using (heq t).symm)
    exact tendsto_nhds_unique (s.pair_w_limit p) h
  have hmetric : ∀ p k, p ≠ k → D p k^2*
      ((s.pairZ p-s.pairZ k)*(s.pairW p-s.pairW k)) = 1 := by
    intro p k hpk
    have hbk : b p ≠ b k := by
      intro he
      apply hpk
      exact Fin.ext (by simpa [b] using congrArg (fun x : Fin 5 => x.val) he)
    have h := ((hD p k).pow 2).mul
      (((hU p).sub (hU k)).mul ((s.pair_w_limit p).sub (s.pair_w_limit k)))
    have heq (t : ℕ) : (q (s.subsequence t)).delta (b p) (b k)^2*
        (((q (s.subsequence t)).inverseScale*(q (s.subsequence t)).z (b p)-
          (q (s.subsequence t)).inverseScale*(q (s.subsequence t)).z (b k))*
        ((q (s.subsequence t)).w (b p)/(q (s.subsequence t)).inverseScale-
          (q (s.subsequence t)).w (b k)/(q (s.subsequence t)).inverseScale)) = 1 := by
      convert (q (s.subsequence t)).distance (b p) (b k) hbk using 1
      field_simp [ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)]
    exact tendsto_nhds_unique h (tendsto_const_nhds.congr'
      (Eventually.of_forall fun t => (heq t).symm))
  exact ⟨s.pairZ,s.pairW,D,fun p k => by simp [D,eq_comm],
    fun p => by simp [D],hforceZ,hforceW,hmetric⟩

theorem ActualLimit.pairSystem_potential (s : ActualLimit m q l I) (hm : ∀ i, 0 < m i) :
    (s.pairSystem hm).toNormalized.potential = (m 3 : ℂ)*m 4*s.pairDelta := by
  rw [NormalizedSystem.potential_eq_unordered]
  simp [NormalizedSystem.unorderedPotential,Fin.sum_univ_succ,ZWSystem.toNormalized,
    ActualLimit.pairSystem]

theorem ActualLimit.complete_potential_split (s : ActualLimit m q l I) (hm : ∀ i, 0 < m i) :
    (s.pairSystem hm).toNormalized.potential+s.triangle.toNormalized.potential = I := by
  rw [s.pairSystem_potential hm]
  exact s.potential_split

end CentralConfigurations.FiveBody.D2
