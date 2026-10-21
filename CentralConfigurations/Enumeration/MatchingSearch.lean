import CentralConfigurations.Enumeration.NormalizedSearch

/-!
# Monochrome reduction followed by simultaneous matching

Algorithm I, Steps I.2--I.3: a certified single-color representative family
replaces the first matrix. The second matrix retains all labelings and is
transported by the same permutation. Filtering before taking the product
reduces the binary-pair search space. The coverage theorem is parameterized
by the representative lists and their certificates.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

def monochromeCandidates (n : ℕ) : Finset (BinaryMatrixCode n) :=
  (BinaryMatrixCode.prefixCandidates n).filter (fun c => monochromeCheck c = true)

def monochromeAllCandidates (n : ℕ) : Finset (BinaryMatrixCode n) :=
  Finset.univ.filter (fun c => monochromeCheck c = true)

/-- Only the first color is replaced by an orbit representative. -/
def MonochromeCovers {n : ℕ} (representatives : Finset (BinaryMatrixCode n)) : Prop :=
  ∀ c ∈ monochromeCandidates n, ∃ r ∈ representatives,
    ∃ e : Equiv.Perm (Fin n), BinaryMatrixCode.relabel c e = r

instance monochromeCovers_decidable {n : ℕ} (representatives : Finset (BinaryMatrixCode n)) :
    Decidable (MonochromeCovers representatives) := by
  unfold MonochromeCovers
  infer_instance

def monochromeCoverageCheck {n : ℕ} (representatives : Finset (BinaryMatrixCode n)) : Bool :=
  decide (MonochromeCovers representatives)

theorem monochromeCoverageCheck_sound {n : ℕ} {representatives : Finset (BinaryMatrixCode n)}
    (h : monochromeCoverageCheck representatives = true) : MonochromeCovers representatives := by
  simpa [monochromeCoverageCheck] using h

/-- All second-color labelings remain present; no independent pair reduction. -/
def matchedCandidates {n : ℕ} (representatives : Finset (BinaryMatrixCode n)) :
    Finset (DiagramCode n) :=
  (representatives.product (monochromeAllCandidates n)).filter
    (fun d => BinaryMatrixCode.trace d.1 ≤ BinaryMatrixCode.trace d.2 ∧
      bicoloredCheck d.1 d.2 = true)

theorem ScaledZWLimit.exists_matched_candidate {n : ℕ} {mass : Fin n → ℝ}
    {q : ℕ → ZWSystem ℂ n (fun i => (mass i : ℂ))}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hm : ∀ i, 0 < mass i)
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : l.z.Nonzero) (hw : l.w.Nonzero)
    (representatives : Finset (BinaryMatrixCode n)) (hc : MonochromeCovers representatives) :
    ∃ d ∈ matchedCandidates representatives, d ∈ DiagramCode.orbit l.diagramCode := by
  let d := DiagramCode.normalize l.diagramCode
  have hd : d ∈ acceptedCandidates n := l.normalize_mem_accepted hm hb ha hz hw
  have hdcheck := (Finset.mem_filter.mp hd).2
  have hdmono : d.1 ∈ monochromeCandidates n := by
    apply Finset.mem_filter.mpr
    exact ⟨DiagramCode.normalized_first_generated _,
      (monochromeCheck_eq_true _).mpr ((candidateCheck_eq_true _ _).mp hdcheck).1.1⟩
  obtain ⟨r, hr, e, he⟩ := hc d.1 hdmono
  let u := DiagramCode.relabel d e
  have huorb : u ∈ DiagramCode.orbit l.diagramCode := by
    apply DiagramCode.orbit_transitive (DiagramCode.normalize_mem_orbit l.diagramCode)
    exact (DiagramCode.mem_orbit_iff d u).mpr ⟨e, false, rfl⟩
  have hucheck : candidateCheck u.1 u.2 = true := by
    obtain ⟨f, s, hfs⟩ := (DiagramCode.mem_orbit_iff _ _).mp huorb
    rw [← hfs]
    exact l.transform_diagramCode_check hm hb ha hz hw f s
  have huconditions := (candidateCheck_eq_true _ _).mp hucheck
  have hufst : u.1 ∈ representatives := by
    change BinaryMatrixCode.relabel d.1 e ∈ representatives
    rw [he]
    exact hr
  have husnd : u.2 ∈ monochromeAllCandidates n := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (monochromeCheck_eq_true _).mpr huconditions.1.2⟩
  have hut : BinaryMatrixCode.trace u.1 ≤ BinaryMatrixCode.trace u.2 := by
    simpa only [u, DiagramCode.relabel, BinaryMatrixCode.trace_relabel] using
      DiagramCode.normalize_trace_order l.diagramCode
  exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hufst, husnd⟩,
    hut, (bicoloredCheck_eq_true _ _).mpr huconditions.2⟩, huorb⟩

/-- Both finite coverage certificates compose with the actual singular-limit
front end. This is a theorem about supplied certificates, not a count of 117. -/
theorem matched_representative_of_positive_gauged_unbounded {n : ℕ} (mass : Fin n → ℝ)
    (q : ℕ → NormalizedSystem ℂ n (fun i => (mass i : ℂ))) (hm : ∀ i, 0 < mass i)
    (i j : Fin n) (hij : i ≠ j) (hg : ∀ t, (q t).InGauge i j)
    (hu : ¬ BddAbove (Set.range
      (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖)))
    (monochromeRepresentatives : Finset (BinaryMatrixCode n))
    (hc : monochromeCoverageCheck monochromeRepresentatives = true)
    (diagramRepresentatives : Finset (DiagramCode n))
    (hd : DiagramCode.coverageCheck (matchedCandidates monochromeRepresentatives)
      diagramRepresentatives = true) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
        atTop (𝓝 0) ∧
      ∃ r ∈ diagramRepresentatives, r ∈ DiagramCode.orbit l.leading.diagramCode := by
  obtain ⟨l, hl, _⟩ := extended_rules_of_gauged_unbounded q
    (complex_positive_masses_admissible mass hm) i j hij hg hu
  obtain ⟨d, hdm, hdo⟩ := l.leading.exists_matched_candidate hm
    (fun t => (q (l.subsequence t)).toZW.balanced_norms i j hij) hl l.z_nonzero l.w_nonzero
    monochromeRepresentatives (monochromeCoverageCheck_sound hc)
  obtain ⟨r, hr, hro⟩ := DiagramCode.coverageCheck_sound hd hdm
  exact ⟨l, hl, r, hr, DiagramCode.orbit_transitive hdo hro⟩

end CentralConfigurations
