import CentralConfigurations.Diagrams.ComponentRules
import CentralConfigurations.Model.SourceCoordinates
import CentralConfigurations.Diagrams.DoubleTriangles
import CentralConfigurations.Diagrams.CycleRules
import CentralConfigurations.Diagrams.BoundaryCuts
import CentralConfigurations.Diagrams.TraceThree
import CentralConfigurations.Diagrams.SourceConnectivity
import CentralConfigurations.Asymptotics.Unbounded
import CentralConfigurations.Diagrams.TraceTwo
import CentralConfigurations.Diagrams.TraceTwoCubic
import CentralConfigurations.Diagrams.GraphComponents
import CentralConfigurations.Diagrams.AppendixComponentFilter

/-!
# Initial matrix restrictions from singular limits

Necessary conditions for normalized, gauged solution sequences imply the
Algorithm I filters in Chang's Theorems 3.1, 3.2, 3.3(a--e), and 3.4--3.8.
Connected-component rules cover both the source definition and the appendix's
finite-set implementation. Theorem 3.5 is stated on four distinct vertices.
The enumeration modules apply these restrictions to finite candidate lists.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

def matrixOutsidePairSum {n : ℕ} (A : Fin n → Fin n → ℕ) (i j : Fin n) : ℕ :=
  ∑ k ∈ Finset.univ.filter (fun k => k ≠ i ∧ k ≠ j), (A k i + A k j)

structure InitialMatrixRules {n : ℕ} (A B : Fin n → Fin n → ℕ) : Prop where
  binaryA : ∀ i j, A i j = 0 ∨ A i j = 1
  binaryB : ∀ i j, B i j = 0 ∨ B i j = 1
  symmetricA : ∀ i j, A i j = A j i
  symmetricB : ∀ i j, B i j = B j i
  columnsA : ∀ j, (∑ i, A i j) ≠ 1
  columnsB : ∀ j, (∑ i, B i j) ≠ 1
  nonzeroA : ∃ j, (∑ i, A i j) ≠ 0
  nonzeroB : ∃ j, (∑ i, B i j) ≠ 0
  traceA : (∑ i, A i i) ≠ 1
  traceB : (∑ i, B i i) ≠ 1
  circlingA : ∀ i j, i ≠ j → A i j * (B i i + B j j) ≠ 1
  circlingB : ∀ i j, i ≠ j → B i j * (A i i + A j j) ≠ 1
  twoColumns : ∀ i j, i ≠ j → A i j + B i j = 2 →
    matrixOutsidePairSum A i j * matrixOutsidePairSum B i j ≠ 0
  secondTrace : (∀ i j, i ≠ j → A i j + B i j ≠ 1) →
    (∑ i, (A i i + B i i)) = 0

theorem ScaledZWLimit.initialMatrixRules {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {a : ℕ → ℂ} (l : ScaledZWLimit q a)
    (ha : Tendsto a atTop (𝓝 0)) (hm : AdmissibleMasses mass)
    (hz : l.z.Nonzero) (hw : l.w.Nonzero) : InitialMatrixRules l.z.matrix l.w.matrix := by
  have hmi : ∀ i, mass i ≠ 0 := by
    intro i
    simpa using hm {i} (by simp)
  exact {
    binaryA := l.z.matrix_binary
    binaryB := l.w.matrix_binary
    symmetricA := l.z.matrix_symm
    symmetricB := l.w.matrix_symm
    columnsA := l.z.column_sum_ne_one hmi
    columnsB := l.w.column_sum_ne_one hmi
    nonzeroA := hz.exists_nonzero_column
    nonzeroB := hw.exists_nonzero_column
    traceA := l.z.trace_ne_one hmi
    traceB := l.w.trace_ne_one hmi
    circlingA := l.z_circling_matrix ha
    circlingB := l.w_circling_matrix ha
    twoColumns := l.two_column_sums ha hm
    secondTrace := l.no_single_edges_trace_zero ha hm
  }

/-- The current end-to-end milestone. The norms in its hypothesis use precisely
the source's upper-pair coordinates. Input is an actual sequence of solutions;
output retains the extracted sequence and its leading matrices. -/
theorem initial_rules_of_gauged_divergence {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → NormalizedSystem ℂ n mass) (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hmax : Tendsto (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖)
      atTop atTop) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      InitialMatrixRules l.leading.z.matrix l.leading.w.matrix := by
  have hh : Tendsto (fun t => max ‖(q t).toZW.zVector‖ ‖(q t).toZW.wVector‖)
      atTop atTop := by
    simpa only [ZWSystem.zVector_norm_eq_source, ZWSystem.wVector_norm_eq_source] using hmax
  obtain ⟨l, hl⟩ := exists_gauged_singular_limit q i j hij hg hh
  exact ⟨l, l.leading.initialMatrixRules hl hm l.z_nonzero l.w_nonzero⟩

/-- The strengthened end-to-end entry point also includes every triangle
filter of Theorem 3.4. The same extracted solution sequence supplies all rules. -/
theorem initial_and_triangle_rules_of_gauged_divergence {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → NormalizedSystem ℂ n mass) (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hmax : Tendsto (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖)
      atTop atTop) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      InitialMatrixRules l.leading.z.matrix l.leading.w.matrix ∧
      TriangleMatrixRules l.leading.z.matrix l.leading.w.matrix := by
  have hh : Tendsto (fun t => max ‖(q t).toZW.zVector‖ ‖(q t).toZW.wVector‖)
      atTop atTop := by
    simpa only [ZWSystem.zVector_norm_eq_source, ZWSystem.wVector_norm_eq_source] using hmax
  obtain ⟨l, hl⟩ := exists_gauged_singular_limit q i j hij hg hh
  exact ⟨l, l.leading.initialMatrixRules hl hm l.z_nonzero l.w_nonzero,
    l.leading.triangleMatrixRules (fun t =>
      (q (l.subsequence t)).toZW.balanced_norms i j hij)⟩

/-- Necessary conditions currently derived from the same actual leading limit.
This record contains conclusions, never hypotheses on candidate matrices. -/
structure ExtendedMatrixRules {n : ℕ} (mass : Fin n → ℂ)
    (A B : Fin n → Fin n → ℕ) : Prop where
  initial : InitialMatrixRules A B
  traceTwoA : TraceTwoRule A
  traceTwoB : TraceTwoRule B
  traceTwoRowsA : TraceTwoCompanionRowsRule A B
  traceTwoRowsB : TraceTwoCompanionRowsRule B A
  traceTwoCubicA : TraceTwoCubicRule mass A B
  traceTwoCubicB : TraceTwoCubicRule mass B A
  traceThreeA : TraceThreeRule A
  traceThreeB : TraceThreeRule B
  triangles : TriangleMatrixRules A B
  quadrilaterals : QuadrilateralMatrixRules A B
  pentagons : PentagonMatrixRule A B
  fullyConnectedA : FullyConnectedCompanionRule A B
  fullyConnectedB : FullyConnectedCompanionRule B A
  algorithmConnectedA : AlgorithmFullyConnectedCompanionRule A B
  algorithmConnectedB : AlgorithmFullyConnectedCompanionRule B A
  isolatedComponentsA : IsolatedComponentMatrixRule A B
  isolatedComponentsB : IsolatedComponentMatrixRule B A
  sourceComponentsA : SourceComponentMatrixRule A B
  sourceComponentsB : SourceComponentMatrixRule B A
  appendixComponentsA : AppendixComponentMatrixRule A B
  appendixComponentsB : AppendixComponentMatrixRule B A
  appendixComponentCheckA : appendixComponentCheck A B = true
  appendixComponentCheckB : appendixComponentCheck B A = true
  cutA : TraceZeroCutRule A
  cutB : TraceZeroCutRule B

theorem ScaledZWLimit.extendedMatrixRules {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hm : AdmissibleMasses mass) (hz : l.z.Nonzero) (hw : l.w.Nonzero) :
    ExtendedMatrixRules mass l.z.matrix l.w.matrix := by
  have hmi : ∀ i, mass i ≠ 0 := by
    intro i
    simpa using hm {i} (by simp)
  have has : Tendsto (fun t => ((q t).swap).inverseScale) atTop (𝓝 0) := by
    change Tendsto (fun t => (‖(q t).wVector‖ : ℂ)⁻¹) atTop (𝓝 0)
    simpa only [ZWSystem.inverseScale, ← hb] using ha
  exact {
    initial := l.initialMatrixRules ha hm hz hw
    traceTwoA := l.trace_two_rule hb hm
    traceTwoB := (l.swapBalanced hb).trace_two_rule (fun t => (hb t).symm) hm
    traceTwoRowsA := l.trace_two_companion_rows_zero ha hm
    traceTwoRowsB := (l.swapBalanced hb).trace_two_companion_rows_zero
      has hm
    traceTwoCubicA := l.trace_two_cubic_rule hb ha hm hw
    traceTwoCubicB := (l.swapBalanced hb).trace_two_cubic_rule
      (fun t => (hb t).symm) has hm hz
    traceThreeA := l.trace_three_rule hb hm
    traceThreeB := (l.swapBalanced hb).trace_three_rule (fun t => (hb t).symm) hm
    triangles := l.triangleMatrixRules hb
    quadrilaterals := l.quadrilateralMatrixRules hb
    pentagons := l.pentagon_matrix_rule hb
    fullyConnectedA := l.source_fully_connected_companion_trace ha hm
    fullyConnectedB := l.swap.source_fully_connected_companion_trace ha hm
    algorithmConnectedA := l.algorithm_fully_connected_companion_trace ha hm
    algorithmConnectedB := l.swap.algorithm_fully_connected_companion_trace ha hm
    isolatedComponentsA := l.isolated_component_matrix_rule ha hm
    isolatedComponentsB := l.swap.isolated_component_matrix_rule ha hm
    sourceComponentsA := l.source_component_matrix_rule ha hm
    sourceComponentsB := l.swap.source_component_matrix_rule ha hm
    appendixComponentsA := l.appendix_component_matrix_rule ha hm
    appendixComponentsB := l.swap.appendix_component_matrix_rule ha hm
    appendixComponentCheckA := l.appendix_component_check ha hm
    appendixComponentCheckB := l.swap.appendix_component_check ha hm
    cutA := l.z.trace_zero_cut_ne_one hmi
    cutB := l.w.trace_zero_cut_ne_one hmi
  }

/-- Source-vector divergence yields one balanced extracted limit satisfying
every currently proved filter: 3.1, 3.2, 3.3(a--e), 3.4,
3.5 (four distinct vertices), 3.6, 3.7 and 3.8, including the actual appendix
component-check expression. -/
theorem extended_rules_of_gauged_divergence {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → NormalizedSystem ℂ n mass) (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hmax : Tendsto (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖)
      atTop atTop) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      ExtendedMatrixRules mass l.leading.z.matrix l.leading.w.matrix := by
  have hh : Tendsto (fun t => max ‖(q t).toZW.zVector‖ ‖(q t).toZW.wVector‖)
      atTop atTop := by
    simpa only [ZWSystem.zVector_norm_eq_source, ZWSystem.wVector_norm_eq_source] using hmax
  obtain ⟨l, hl⟩ := exists_gauged_singular_limit q i j hij hg hh
  exact ⟨l, l.leading.extendedMatrixRules
    (fun t => (q (l.subsequence t)).toZW.balanced_norms i j hij) hl hm l.z_nonzero l.w_nonzero⟩

/-- The current front-end entry point requires only unbounded source-vector
norms. The resulting strict subsequence, common vanishing scale, and all proved
matrix restrictions are retained together. -/
theorem extended_rules_of_gauged_unbounded {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → NormalizedSystem ℂ n mass) (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hu : ¬ BddAbove (Set.range
      (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖))) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
        atTop (𝓝 0) ∧ ExtendedMatrixRules mass l.leading.z.matrix l.leading.w.matrix := by
  obtain ⟨l, hl⟩ := exists_gauged_singular_limit_of_unbounded q i j hij hg hu
  exact ⟨l, hl, l.leading.extendedMatrixRules
    (fun t => (q (l.subsequence t)).toZW.balanced_norms i j hij) hl hm l.z_nonzero l.w_nonzero⟩

end CentralConfigurations
