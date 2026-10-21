import CentralConfigurations.Diagrams.MatrixReachability

/-!
# Connected-component rules using the literal source definition

An all-positive principal submatrix need not be identified with an ordinary
graph component. The proof only needs equality of their circled-vertex sets.
A loop pads every simple path, so maximality includes all circles in the
ordinary component. Its already-proved mass balance then gives Theorem 3.7(b).
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

/-- A subset retains every nonzero diagonal entry of a larger set. -/
def MatrixCircleCover {n : ℕ} (A : Fin n → Fin n → ℕ)
    (s c : Finset (Fin n)) : Prop :=
  s ⊆ c ∧ ∀ i ∈ c, A i i ≠ 0 → i ∈ s

def ComponentMatrixConclusion {n : ℕ} (A B : Fin n → Fin n → ℕ)
    (s : Finset (Fin n)) : Prop :=
  (∑ i ∈ s, A i i) ≠ 1 ∧
    (s.Nonempty → (∀ i ∈ s, A i i = 1) →
      ∃ i ∈ s, ∃ j ∈ s, i ≠ j ∧ A i j + B i j ≠ 2)

/-- Isolation is needed only for the larger set; the tested set must retain
all of its circles. This is the mass-balance argument used in Theorem 3.7(b). -/
theorem ScaledZWLimit.component_conclusion_of_circle_cover {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass)
    (s c : Finset (Fin n)) (his : MatrixIsolated l.z.matrix c)
    (hc : MatrixCircleCover l.z.matrix s c) :
    ComponentMatrixConclusion l.z.matrix l.w.matrix s := by
  classical
  have hmi : ∀ i, mass i ≠ 0 := by
    intro i
    simpa using hm {i} (by simp)
  have htr : (∑ i ∈ s, l.z.matrix i i) = ∑ i ∈ c, l.z.matrix i i := by
    apply Finset.sum_subset hc.1
    intro i hic his
    by_contra hn
    exact his (hc.2 i hic hn)
  refine ⟨fun h => l.z.isolated_trace_ne_one hmi c his (htr.symm.trans h), ?_⟩
  intro hne hall
  by_contra hn
  obtain ⟨i, hi⟩ := hne
  have hip : l.z.position i ≠ 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hall i hi
  apply hip
  apply l.z.coincident_component_circles_zero hm c i (hc.1 hi) (l.z.matrix_isolated_force his)
  intro j hj hjp
  have hjs : j ∈ s := hc.2 j hj (by
    simp [OneColorLimit.matrix, OneColorLimit.Incident, hjp])
  by_cases hji : j = i
  · exact congrArg l.z.position hji
  have hd : l.z.matrix j i + l.w.matrix j i = 2 := by
    by_contra h
    exact hn ⟨j, hjs, i, hi, hji, h⟩
  have hw : l.w.matrix j i = 1 := by
    have := l.z.matrix_binary j i
    have := l.w.matrix_binary j i
    omega
  apply l.w_stroke_z_close ha j i hji
  simpa [OneColorLimit.matrix, OneColorLimit.Incident, hji] using hw

/-- Nonempty connected components in Definition 3.2, with the printed
`A^(n+1)-I` and literal inclusion-maximal principal positivity. -/
structure SourceConnectedComponent {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (s : Finset (Fin n)) : Prop where
  nonempty : s.Nonempty
  positive : SourcePrincipalPositive A s
  maximal : ∀ t : Finset (Fin n), s ⊆ t → SourcePrincipalPositive A t → t = s

theorem sourceConnectivityMatrix_symm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℕ)
    (hs : ∀ i j, A i j = A j i) (i j : Fin n) :
    sourceConnectivityMatrix A i j = sourceConnectivityMatrix A j i := by
  by_cases hij : i = j
  · subst j; rfl
  · simp only [sourceConnectivityMatrix, Matrix.sub_apply, Matrix.one_apply,
      if_neg hij, if_neg (Ne.symm hij), sub_zero]
    exact integerMatrix_pow_symm A hs (n + 1) i j

theorem OneColorLimit.circle_source_diagonal_pos {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (i : Fin n) (hi : q.matrix i i = 1) :
    0 < sourceConnectivityMatrix q.matrix i i := by
  have hp : q.position i ≠ 0 := by simpa [matrix, Incident] using hi
  obtain ⟨j, hji, hf⟩ := q.circle_has_stroke i hp
  have he : q.matrix i j = 1 := by simp [matrix, Incident, hji.symm, hf]
  have hn : 2 ≤ n + 1 := by have := i.isLt; omega
  have h := loop_neighbor_power_diagonal q.matrix q.matrix_symm i j hji.symm hi he (n + 1) hn
  change 0 < (integerMatrix q.matrix ^ (n + 1)) i i - (1 : Matrix (Fin n) (Fin n) ℤ) i i
  simpa only [Matrix.one_apply_eq] using (by omega :
    0 < (integerMatrix q.matrix ^ (n + 1)) i i - 1)

theorem OneColorLimit.circle_source_entry_pos {n : ℕ} {mass : Fin n → ℂ}
    (q : OneColorLimit ℂ n mass) (i j : Fin n) (hj : q.matrix j j = 1)
    (h : (offDiagonalGraph q.matrix q.matrix_symm).Reachable i j) :
    0 < sourceConnectivityMatrix q.matrix i j := by
  by_cases hij : i = j
  · subst i
    exact q.circle_source_diagonal_pos j hj
  · have hp := reachable_loop_power_pos q.matrix q.matrix_symm i j h hj (n + 1) (by omega)
    simpa only [sourceConnectivityMatrix, Matrix.sub_apply, Matrix.one_apply,
      if_neg hij, sub_zero] using hp

/-- Every source component retains exactly the circles of its ordinary
component. Full equality of the vertex sets is not required. -/
theorem SourceConnectedComponent.circle_cover {n : ℕ} {mass : Fin n → ℂ}
    {q : OneColorLimit ℂ n mass} {s : Finset (Fin n)}
    (h : SourceConnectedComponent q.matrix s) (i : Fin n) (hi : i ∈ s) :
    MatrixCircleCover q.matrix s (ordinaryComponent q.matrix q.matrix_symm i) := by
  classical
  have hs : s ⊆ ordinaryComponent q.matrix q.matrix_symm i := by
    intro j hj
    apply (mem_ordinaryComponent _ _ _ _).mpr
    exact integerMatrix_pow_reachable q.matrix q.matrix_symm (n + 1) i j
      (h.positive.power_nonzero i hi j hj)
  refine ⟨hs, ?_⟩
  intro r hrc hr
  have hrr : q.matrix r r = 1 := (q.matrix_binary r r).resolve_left hr
  have hreach := (mem_ordinaryComponent _ _ _ _).mp hrc
  have hsr : ∀ j ∈ s, 0 < sourceConnectivityMatrix q.matrix j r := by
    intro j hj
    exact q.circle_source_entry_pos j r hrr
      (((mem_ordinaryComponent _ _ _ _).mp (hs hj)).symm.trans hreach)
  have hrs : ∀ j ∈ s, 0 < sourceConnectivityMatrix q.matrix r j := by
    intro j hj
    rw [sourceConnectivityMatrix_symm q.matrix q.matrix_symm r j]
    exact hsr j hj
  have hins : SourcePrincipalPositive q.matrix (insert r s) := by
    intro u hu v hv
    rcases Finset.mem_insert.mp hu with hur | hus
    · rw [hur]
      rcases Finset.mem_insert.mp hv with hvr | hvs
      · rw [hvr]
        exact q.circle_source_diagonal_pos r hrr
      · exact hrs v hvs
    · rcases Finset.mem_insert.mp hv with hvr | hvs
      · rw [hvr]
        exact hsr u hus
      · exact h.positive u hus v hvs
  have heq := h.maximal (insert r s) (Finset.subset_insert r s) hins
  rw [← heq]
  exact Finset.mem_insert_self r s

def SourceComponentMatrixRule {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℕ) : Prop :=
  ∀ s, SourceConnectedComponent A s → ComponentMatrixConclusion A B s

/-- Theorem 3.7(b) for the literal nonempty source components. -/
theorem ScaledZWLimit.source_component_matrix_rule {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass) :
    SourceComponentMatrixRule l.z.matrix l.w.matrix := by
  intro s hs
  obtain ⟨i, hi⟩ := hs.nonempty
  exact l.component_conclusion_of_circle_cover ha hm s
    (ordinaryComponent l.z.matrix l.z.matrix_symm i)
    (ordinaryComponent_isolated l.z.matrix l.z.matrix_symm i) (hs.circle_cover i hi)

end CentralConfigurations
