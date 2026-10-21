import CentralConfigurations.Diagrams.InitialRules
import CentralConfigurations.Enumeration.BinaryMatrices
import Mathlib.Data.Fintype.Powerset

/-!
# Executable necessary-condition filters for Algorithm I

These checks directly implement the proved matrix rules on finite codes.
They use all index orderings, with distinctness premises, rather than the
appendix's optimized subloops. Equivalence of an optimized implementation
must be proved separately. The mass-dependent trace exclusion is discharged
here for positive real masses; it is not assumed for arbitrary complex masses.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

def MonochromeConditions {n : ℕ} (A : Fin n → Fin n → ℕ) : Prop :=
  (∀ j, (∑ i, A i j) ≠ 1) ∧ (∃ j, (∑ i, A i j) ≠ 0) ∧
  (∑ i, A i i) ≠ 1 ∧ TraceTwoRule A ∧ MonochromeTriangleRules A ∧
  FirstQuadrilateralRule A ∧ TraceThreeRule A ∧ TraceZeroCutRule A

set_option synthInstance.maxSize 2048 in
instance monochromeConditions_decidable {n : ℕ} (A : Fin n → Fin n → ℕ) :
    Decidable (MonochromeConditions A) := by
  unfold MonochromeConditions TraceTwoRule MonochromeTriangleRules
    FirstQuadrilateralRule TraceThreeRule TraceZeroCutRule
  infer_instance

def PositiveTraceTwoExclusion {n : ℕ} (A B : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j, i ≠ j → (∑ r, A r r) = 2 → A i i = 1 → A j j = 1 →
    (∀ r, r ≠ i → r ≠ j → A i r = 0 ∧ A j r = 0) → (∑ r, B r r) ≠ n - 3

def BicoloredConditions {n : ℕ} (A B : Fin n → Fin n → ℕ) : Prop :=
  (∀ i j, i ≠ j → A i j * (B i i + B j j) ≠ 1) ∧
  (∀ i j, i ≠ j → B i j * (A i i + A j j) ≠ 1) ∧
  TraceTwoCompanionRowsRule A B ∧ TraceTwoCompanionRowsRule B A ∧
  PositiveTraceTwoExclusion A B ∧ PositiveTraceTwoExclusion B A ∧
  ColoredTriangleRules A B ∧
  (∀ i j, i ≠ j → A i j + B i j = 2 →
    matrixOutsidePairSum A i j * matrixOutsidePairSum B i j ≠ 0) ∧
  SecondQuadrilateralRule A B ∧ PentagonMatrixRule A B ∧
  AlgorithmFullyConnectedCompanionRule A B ∧ AlgorithmFullyConnectedCompanionRule B A ∧
  appendixComponentCheck A B = true ∧ appendixComponentCheck B A = true ∧
  ((∀ i j, i ≠ j → A i j + B i j ≠ 1) → (∑ i, (A i i + B i i)) = 0)

set_option synthInstance.maxSize 16384 in
instance bicoloredConditions_decidable {n : ℕ} (A B : Fin n → Fin n → ℕ) :
    Decidable (BicoloredConditions A B) := by
  unfold BicoloredConditions TraceTwoCompanionRowsRule PositiveTraceTwoExclusion
    ColoredTriangleRules SecondQuadrilateralRule PentagonMatrixRule Function.Injective
    AlgorithmFullyConnectedCompanionRule AlgorithmFullyConnected
  infer_instance

def monochromeCheck {n : ℕ} (c : BinaryMatrixCode n) : Bool :=
  decide (MonochromeConditions (BinaryMatrixCode.decode c))

def bicoloredCheck {n : ℕ} (c d : BinaryMatrixCode n) : Bool :=
  decide (BicoloredConditions (BinaryMatrixCode.decode c) (BinaryMatrixCode.decode d))

def candidateCheck {n : ℕ} (c d : BinaryMatrixCode n) : Bool :=
  monochromeCheck c && monochromeCheck d && bicoloredCheck c d

@[simp] theorem monochromeCheck_eq_true {n : ℕ} (c : BinaryMatrixCode n) :
    monochromeCheck c = true ↔ MonochromeConditions (BinaryMatrixCode.decode c) := by
  simp [monochromeCheck]

@[simp] theorem bicoloredCheck_eq_true {n : ℕ} (c d : BinaryMatrixCode n) :
    bicoloredCheck c d = true ↔
      BicoloredConditions (BinaryMatrixCode.decode c) (BinaryMatrixCode.decode d) := by
  simp [bicoloredCheck]

@[simp] theorem candidateCheck_eq_true {n : ℕ} (c d : BinaryMatrixCode n) :
    candidateCheck c d = true ↔
      (MonochromeConditions (BinaryMatrixCode.decode c) ∧
        MonochromeConditions (BinaryMatrixCode.decode d)) ∧
      BicoloredConditions (BinaryMatrixCode.decode c) (BinaryMatrixCode.decode d) := by
  simp [candidateCheck]

theorem positive_complex_cube_sum_ne_zero {n : ℕ} (mass : Fin n → ℝ)
    (hm : ∀ i, 0 < mass i) (i j : Fin n) :
    (mass i : ℂ) ^ 3 + (mass j : ℂ) ^ 3 ≠ 0 := by
  exact_mod_cast ne_of_gt (add_pos (pow_pos (hm i) 3) (pow_pos (hm j) 3))

theorem ExtendedMatrixRules.monochrome_conditions {n : ℕ} {mass : Fin n → ℂ}
    {A B : Fin n → Fin n → ℕ} (h : ExtendedMatrixRules mass A B) :
    MonochromeConditions A ∧ MonochromeConditions B := by
  exact ⟨⟨h.initial.columnsA, h.initial.nonzeroA, h.initial.traceA, h.traceTwoA,
      h.triangles.monochromeA, h.quadrilaterals.firstA, h.traceThreeA, h.cutA⟩,
    ⟨h.initial.columnsB, h.initial.nonzeroB, h.initial.traceB, h.traceTwoB,
      h.triangles.monochromeB, h.quadrilaterals.firstB, h.traceThreeB, h.cutB⟩⟩

theorem ExtendedMatrixRules.bicolored_conditions {n : ℕ} {mass : Fin n → ℝ}
    {A B : Fin n → Fin n → ℕ} (h : ExtendedMatrixRules (fun i => (mass i : ℂ)) A B)
    (hm : ∀ i, 0 < mass i) : BicoloredConditions A B := by
  have hcA : PositiveTraceTwoExclusion A B := by
    intro i j hij ht hi hj he
    exact h.traceTwoCubicA i j hij ht hi hj he (positive_complex_cube_sum_ne_zero mass hm i j)
  have hcB : PositiveTraceTwoExclusion B A := by
    intro i j hij ht hi hj he
    exact h.traceTwoCubicB i j hij ht hi hj he (positive_complex_cube_sum_ne_zero mass hm i j)
  exact ⟨h.initial.circlingA, h.initial.circlingB, h.traceTwoRowsA, h.traceTwoRowsB,
    hcA, hcB, h.triangles.colored, h.initial.twoColumns, h.quadrilaterals.second,
    h.pentagons, h.algorithmConnectedA, h.algorithmConnectedB,
    h.appendixComponentCheckA, h.appendixComponentCheckB, h.initial.secondTrace⟩

theorem ExtendedMatrixRules.candidate_check {n : ℕ} {mass : Fin n → ℝ}
    {A B : Fin n → Fin n → ℕ} (h : ExtendedMatrixRules (fun i => (mass i : ℂ)) A B)
    (hm : ∀ i, 0 < mass i) :
    candidateCheck (BinaryMatrixCode.encode A) (BinaryMatrixCode.encode B) = true := by
  have ha := BinaryMatrixCode.decode_encode A h.initial.binaryA h.initial.symmetricA
  have hb := BinaryMatrixCode.decode_encode B h.initial.binaryB h.initial.symmetricB
  simp only [candidateCheck, Bool.and_eq_true, monochromeCheck_eq_true,
    bicoloredCheck_eq_true, ha, hb]
  exact ⟨⟨h.monochrome_conditions.1, h.monochrome_conditions.2⟩, h.bicolored_conditions hm⟩

/-- The executable predicate receives actual finite codes from one extracted
sequence. This is not yet the optimized enumeration or the count 117. -/
theorem candidate_check_of_positive_gauged_unbounded {n : ℕ} (mass : Fin n → ℝ)
    (q : ℕ → NormalizedSystem ℂ n (fun i => (mass i : ℂ))) (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hu : ¬ BddAbove (Set.range
      (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖))) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
        atTop (𝓝 0) ∧
      ∃ c d : BinaryMatrixCode n, BinaryMatrixCode.decode c = l.leading.z.matrix ∧
        BinaryMatrixCode.decode d = l.leading.w.matrix ∧ candidateCheck c d = true := by
  obtain ⟨l, hl, hr⟩ := extended_rules_of_gauged_unbounded q
    (complex_positive_masses_admissible mass hm) i j hij hg hu
  exact ⟨l, hl, BinaryMatrixCode.encode _, BinaryMatrixCode.encode _,
    BinaryMatrixCode.decode_encode _ hr.initial.binaryA hr.initial.symmetricA,
    BinaryMatrixCode.decode_encode _ hr.initial.binaryB hr.initial.symmetricB,
    hr.candidate_check hm⟩

end CentralConfigurations
