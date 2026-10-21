import CentralConfigurations.Model.SourceCoordinates

/-!
# From an arbitrary unbounded gauged sequence to a singular limit

This supplies the subsequence step in Section 2.2 of Chang (2023). The input
only asserts that the source-vector maximum norm has no upper bound. It need
not already tend to infinity. Both extractions retain their composition as
a strict subsequence of the original sequence. The implication from infinitely
many gauged solutions to this input is proved in `AlgebraicUnbounded.lean`.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter

theorem unbounded_real_frequently_gt {f : ℕ → ℝ}
    (h : ∀ R : ℝ, ∃ t, R < f t) (R : ℝ) : ∃ᶠ t in atTop, R < f t := by
  rw [frequently_atTop]
  intro N
  let M : ℝ := ∑ k ∈ Finset.range (N + 1), |f k|
  obtain ⟨t, ht⟩ := h (max R M)
  refine ⟨t, ?_, (le_max_left R M).trans_lt ht⟩
  by_contra hNt
  have htmem : t ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hb : |f t| ≤ M :=
    Finset.single_le_sum (fun k _ => abs_nonneg (f k)) htmem
  have hc := le_max_right R M
  have hd := le_abs_self (f t)
  linarith

/-- A strict subsequence diverges, even when the original sequence oscillates. -/
theorem unbounded_real_subsequence (f : ℕ → ℝ)
    (h : ¬ BddAbove (Set.range f)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (fun t => f (φ t)) atTop atTop := by
  have hlarge : ∀ R : ℝ, ∃ t, R < f t := by
    intro R
    obtain ⟨x, ⟨t, rfl⟩, hx⟩ := not_bddAbove_iff.mp h R
    exact ⟨t, hx⟩
  obtain ⟨φ, hφ, hg⟩ := extraction_forall_of_frequently
    (fun n : ℕ => unbounded_real_frequently_gt hlarge (n : ℝ))
  exact ⟨φ, hφ, tendsto_atTop_mono (fun t => (hg t).le) tendsto_natCast_atTop_atTop⟩

/-- Compose the two strict extractions without losing the original source. -/
def ExtractedZWLimit.liftSubsequence {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (l : ExtractedZWLimit (fun t => q (φ t))) : ExtractedZWLimit q where
  subsequence := φ ∘ l.subsequence
  strictMono := hφ.comp l.strictMono
  leading := l.leading
  z_nonzero := l.z_nonzero
  w_nonzero := l.w_nonzero

/-- Arbitrary unboundedness of the original source vectors is sufficient for
a nonzero two-color limit whose common scale tends to zero. -/
theorem exists_gauged_singular_limit_of_unbounded {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → NormalizedSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j)
    (hg : ∀ t, (q t).InGauge i j)
    (hu : ¬ BddAbove (Set.range
      (fun t => max ‖(q t).toZW.zSourceVector‖ ‖(q t).toZW.wSourceVector‖))) :
    ∃ l : ExtractedZWLimit (fun t => (q t).toZW.balanced i j hij),
      Tendsto (fun t => ((q (l.subsequence t)).toZW.balanced i j hij).inverseScale)
        atTop (𝓝 0) := by
  obtain ⟨φ, hφ, hdiv⟩ := unbounded_real_subsequence _ hu
  have hnorm : Tendsto
      (fun t => max ‖(q (φ t)).toZW.zVector‖ ‖(q (φ t)).toZW.wVector‖) atTop atTop := by
    simpa only [ZWSystem.zVector_norm_eq_source, ZWSystem.wVector_norm_eq_source] using hdiv
  obtain ⟨l, hl⟩ := exists_gauged_singular_limit (fun t => q (φ t)) i j hij
    (fun t => hg (φ t)) hnorm
  exact ⟨l.liftSubsequence φ hφ, hl⟩

end CentralConfigurations
