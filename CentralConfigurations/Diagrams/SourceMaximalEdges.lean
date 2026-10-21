import CentralConfigurations.Diagrams.SourceComponents

/-!
# Maximal strokes in the literal source components

For Proposition 4.8 the printed matrix-power component must retain maximal
strokes, not just circles. A circled vertex and its stroke neighbors belong
to the same maximal positive principal submatrix. The small-cardinality
case follows from force balance; it is not excluded by an extra assumption.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

theorem integerMatrix_pow_neighbor_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (i j : Fin n) (he : A i j = 1) (k : ℕ) :
    (integerMatrix A ^ k) i i ≤ (integerMatrix A ^ (k + 2)) j j := by
  have h₁ : (integerMatrix A ^ k) i i ≤ (integerMatrix A ^ (k + 1)) j i := by
    rw [pow_succ', Matrix.mul_apply]
    have h := Finset.single_le_sum
      (fun r (_ : r ∈ Finset.univ) =>
        mul_nonneg (Int.natCast_nonneg (A j r)) (integerMatrix_pow_nonneg A k r i))
      (Finset.mem_univ i)
    simpa [integerMatrix, hs j i, he] using h
  have h₂ : (integerMatrix A ^ (k + 1)) j i ≤ (integerMatrix A ^ (k + 2)) j j := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ, Matrix.mul_apply]
    have h := Finset.single_le_sum
      (fun r (_ : r ∈ Finset.univ) =>
        mul_nonneg (integerMatrix_pow_nonneg A (k + 1) j r) (Int.natCast_nonneg (A r j)))
      (Finset.mem_univ i)
    simpa [integerMatrix, he] using h
  exact h₁.trans h₂

theorem SourceConnectedComponent.mem_of_circle_neighbor_large {n : ℕ} {mass : Fin n → ℂ}
    {q : OneColorLimit ℂ n mass} {s : Finset (Fin n)}
    (h : SourceConnectedComponent q.matrix s) (hn : 3 ≤ n)
    (i : Fin n) (hi : i ∈ s) (hii : q.matrix i i = 1)
    (j : Fin n) (hij : i ≠ j) (he : q.matrix i j = 1) : j ∈ s := by
  have hdiag : 0 < sourceConnectivityMatrix q.matrix j j := by
    have hpow := (loop_neighbor_power_diagonal q.matrix q.matrix_symm i j hij hii he
      (n - 1) (by omega)).trans
      (integerMatrix_pow_neighbor_bound q.matrix q.matrix_symm i j he (n - 1))
    rw [show n - 1 + 2 = n + 1 by omega] at hpow
    change 0 < (integerMatrix q.matrix ^ (n + 1)) j j -
      (1 : Matrix (Fin n) (Fin n) ℤ) j j
    simpa only [Matrix.one_apply_eq] using (by omega :
      0 < (integerMatrix q.matrix ^ (n + 1)) j j - 1)
  have hcross : ∀ v ∈ s, 0 < sourceConnectivityMatrix q.matrix v j := by
    intro v hv
    by_cases hvj : v = j
    · subst v; exact hdiag
    have hr := integerMatrix_pow_reachable q.matrix q.matrix_symm (n + 1) v i
      (h.positive.power_nonzero v hv i hi)
    have hp := reachable_loop_power_pos q.matrix q.matrix_symm v i hr hii n (by omega)
    have hnext : 0 < (integerMatrix q.matrix ^ (n + 1)) v j := by
      rw [pow_succ, Matrix.mul_apply]
      have hbound := Finset.single_le_sum
        (fun r (_ : r ∈ Finset.univ) =>
          mul_nonneg (integerMatrix_pow_nonneg q.matrix n v r) (Int.natCast_nonneg (q.matrix r j)))
        (Finset.mem_univ i)
      apply hp.trans_le
      simpa [integerMatrix, he] using hbound
    simpa only [sourceConnectivityMatrix, Matrix.sub_apply, Matrix.one_apply,
      if_neg hvj, sub_zero] using hnext
  have hins : SourcePrincipalPositive q.matrix (insert j s) := by
    intro u hu v hv
    rcases Finset.mem_insert.mp hu with huj | hus
    · rw [huj]
      rcases Finset.mem_insert.mp hv with hvj | hvs
      · rw [hvj]; exact hdiag
      · rw [sourceConnectivityMatrix_symm q.matrix q.matrix_symm j v]
        exact hcross v hvs
    · rcases Finset.mem_insert.mp hv with hvj | hvs
      · rw [hvj]; exact hcross u hus
      · exact h.positive u hus v hvs
  rw [← h.maximal (insert j s) (Finset.subset_insert j s) hins]
  exact Finset.mem_insert_self j s

theorem OneColorLimit.three_le_of_uncircled_stroke {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (i j : Fin n) (hij : i ≠ j)
    (hm : mass i ≠ 0) (hf : q.force i j ≠ 0) (hj : q.position j = 0) : 3 ≤ n := by
  by_contra hn
  have hji : q.force j i ≠ 0 := by rw [q.antisymm j i]; exact neg_ne_zero.mpr hf
  have hp := q.single_stroke_circled j i hm hji (by
    intro k hki
    have hkj : k = j := by
      apply Fin.ext
      have hi' := i.isLt
      have hj' := j.isLt
      have hk' := k.isLt
      have hne : i.val ≠ j.val := fun e => hij (Fin.ext e)
      have hne' : k.val ≠ i.val := fun e => hki (Fin.ext e)
      omega
    simpa only [hkj] using q.diagonal j)
  exact hp hj

/-- A source component contains every stroke neighbor of each of its circles. -/
theorem SourceConnectedComponent.mem_of_circle_neighbor {n : ℕ} {mass : Fin n → ℂ}
    {q : OneColorLimit ℂ n mass} {s : Finset (Fin n)}
    (h : SourceConnectedComponent q.matrix s) (hm : AdmissibleMasses mass)
    (i : Fin n) (hi : i ∈ s) (hp : q.position i ≠ 0)
    (j : Fin n) (hf : q.force i j ≠ 0) : j ∈ s := by
  have hij : i ≠ j := by intro e; subst j; exact hf (q.diagonal i)
  have he : q.matrix i j = 1 := by simp [OneColorLimit.matrix, OneColorLimit.Incident, hij, hf]
  by_cases hj : q.position j = 0
  · have hmi : mass i ≠ 0 := by simpa using hm {i} (by simp)
    exact h.mem_of_circle_neighbor_large (q.three_le_of_uncircled_stroke i j hij hmi hf hj)
      i hi (by simp [OneColorLimit.matrix, OneColorLimit.Incident, hp]) j hij he
  · apply (h.circle_cover i hi).2 j
    · exact (mem_ordinaryComponent _ _ _ _).mpr
        (matrix_entry_reachable q.matrix q.matrix_symm i j (by omega))
    · simp [OneColorLimit.matrix, OneColorLimit.Incident, hj]

theorem SourceConnectedComponent.maximal_stroke_endpoints_mem {n : ℕ} {mass : Fin n → ℂ}
    {q : OneColorLimit ℂ n mass} {s : Finset (Fin n)}
    (h : SourceConnectedComponent q.matrix s) (hm : AdmissibleMasses mass)
    (r : Fin n) (hr : r ∈ s) (i j : Fin n)
    (hi : i ∈ ordinaryComponent q.matrix q.matrix_symm r)
    (hj : j ∈ ordinaryComponent q.matrix q.matrix_symm r)
    (hf : q.force i j ≠ 0) (hp : q.position i ≠ q.position j) : i ∈ s ∧ j ∈ s := by
  by_cases hip : q.position i = 0
  · have hjp : q.position j ≠ 0 := fun e => hp (hip.trans e.symm)
    have hjs : j ∈ s := (h.circle_cover r hr).2 j hj (by
      simp [OneColorLimit.matrix, OneColorLimit.Incident, hjp])
    have hfi : q.force j i ≠ 0 := by rw [q.antisymm j i]; exact neg_ne_zero.mpr hf
    exact ⟨h.mem_of_circle_neighbor hm j hjs hjp i hfi, hjs⟩
  · have his : i ∈ s := (h.circle_cover r hr).2 i hi (by
      simp [OneColorLimit.matrix, OneColorLimit.Incident, hip])
    exact ⟨his, h.mem_of_circle_neighbor hm i his hip j hf⟩

theorem SourceConnectedComponent.exists_maximal_stroke {n : ℕ} {mass : Fin n → ℂ}
    {q : OneColorLimit ℂ n mass} {s : Finset (Fin n)}
    (h : SourceConnectedComponent q.matrix s) (hm : AdmissibleMasses mass)
    (hc : ∃ r ∈ s, q.position r ≠ 0) :
    ∃ i ∈ s, ∃ j ∈ s, q.force i j ≠ 0 ∧ q.position i ≠ q.position j := by
  obtain ⟨r, hr, hp⟩ := hc
  let c := ordinaryComponent q.matrix q.matrix_symm r
  have hrc : r ∈ c := (mem_ordinaryComponent _ _ _ _).mpr .rfl
  obtain ⟨i, hi, j, hj, hf, hij⟩ :=
    (q.component_maximal_iff_circle hm c
      (q.matrix_isolated_force (ordinaryComponent_isolated _ _ r))).mpr ⟨r, hrc, hp⟩
  have hs := h.maximal_stroke_endpoints_mem hm r hr i j hi hj hf hij
  exact ⟨i, hs.1, j, hs.2, hf, hij⟩

/-- An unordered unique single edge inside a source component containing a
circle is maximal. This is the geometric assertion behind Proposition 4.8(a). -/
theorem ScaledZWLimit.unique_source_z_edge_maximal {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass)
    (s : Finset (Fin n)) (hs : SourceConnectedComponent l.z.matrix s)
    (hc : ∃ r ∈ s, l.z.position r ≠ 0) (i j : Fin n)
    (hu : ∀ u ∈ s, ∀ v ∈ s, u ≠ v → l.z.matrix u v = 1 → l.w.matrix u v = 0 →
      (u = i ∧ v = j) ∨ (u = j ∧ v = i)) : l.z.position i ≠ l.z.position j := by
  obtain ⟨u, hus, v, hvs, hf, hp⟩ := hs.exists_maximal_stroke hm hc
  have huv : u ≠ v := fun e => hp (congrArg l.z.position e)
  have hw : l.w.force u v = 0 := by
    by_contra hn
    exact hp (l.w_stroke_z_close ha u v huv hn)
  have hz : l.z.matrix u v = 1 := by
    simp [OneColorLimit.matrix, OneColorLimit.Incident, huv, hf]
  have hw' : l.w.matrix u v = 0 := by
    simp [OneColorLimit.matrix, OneColorLimit.Incident, huv, hw]
  rcases hu u hus v hvs huv hz hw' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hp
  · exact hp.symm

end CentralConfigurations
