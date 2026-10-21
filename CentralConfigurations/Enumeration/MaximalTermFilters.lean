import CentralConfigurations.Asymptotics.TwoRowMaxima
import CentralConfigurations.Enumeration.DistanceOrderDomains

/-!
# Filters from certified maximal-order comparisons

MaxOrderZ/MaxOrderW delete terms using certified strict comparisons.
The row-count and paired-row distance checks preserve actual order
assignments under these deletions. SourceRowComparisons.lean supplies
the comparison certificates for the source routines.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

def SoundDominanceTable {ι : Type*} (f : ι → ℕ → ℂ) (less : ι → ι → Bool) : Prop :=
  ∀ i j, less i j = true → f i =o[atTop] f j

def dominanceCandidates {n : ℕ} (less : Fin n → Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ j, less i j = false

def dominanceDelete {ι : Type*} [DecidableEq ι] (less : ι → ι → Bool)
    (M : Finset ι) (p : ι × ι) : Finset ι := if less p.1 p.2 then M.erase p.1 else M

def dominanceSweep {ι : Type*} [DecidableEq ι] (less : ι → ι → Bool)
    (pairs : List (ι × ι)) (M : Finset ι) : Finset ι := pairs.foldl (dominanceDelete less) M

theorem maximalTermCover_univ {ι : Type*} [Fintype ι] (f : ι → ℕ → ℂ) :
    MaximalTermCover f Finset.univ := by intro i hi; exact (hi (Finset.mem_univ i)).elim

theorem MaximalTermCover.erase_of_littleO {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℕ → ℂ} {M : Finset ι} (h : MaximalTermCover f M) {i j : ι}
    (hij : f i =o[atTop] f j) : MaximalTermCover f (M.erase i) := by
  intro k hk
  by_cases hki : k = i
  · exact ⟨j, hki ▸ hij⟩
  · exact h k (by simpa [Finset.mem_erase, hki] using hk)

theorem MaximalTermCover.dominanceDelete {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℕ → ℂ} {M : Finset ι} (h : MaximalTermCover f M)
    {less : ι → ι → Bool} (hs : SoundDominanceTable f less) (p : ι × ι) :
    MaximalTermCover f (dominanceDelete less M p) := by
  unfold CentralConfigurations.dominanceDelete
  split_ifs with hp
  · exact h.erase_of_littleO (hs p.1 p.2 hp)
  · exact h

theorem MaximalTermCover.dominanceSweep {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℕ → ℂ} {M : Finset ι} (h : MaximalTermCover f M)
    {less : ι → ι → Bool} (hs : SoundDominanceTable f less) (pairs : List (ι × ι)) :
    MaximalTermCover f (dominanceSweep less pairs M) := by
  induction pairs generalizing M with
  | nil => exact h
  | cons p pairs ih => exact ih (h.dominanceDelete hs p)

theorem SoundDominanceTable.candidates_cover {n : ℕ} {f : Fin n → ℕ → ℂ}
    {less : Fin n → Fin n → Bool} (h : SoundDominanceTable f less) :
    MaximalTermCover f (dominanceCandidates less) := by
  intro i hi
  simp only [dominanceCandidates, Finset.mem_filter, Finset.mem_univ, true_and,
    not_forall] at hi
  obtain ⟨j, hj⟩ := hi
  exact ⟨j, h i j (by cases h' : less i j <;> simp_all)⟩

def maximalRowCountCheck {n : ℕ} (Mz Mw : Fin n → Finset (Fin n)) : Bool :=
  decide (∀ i, (Mz i).card ≠ 1 ∧ (Mw i).card ≠ 1)

def maximalPairDistanceCheck {n : ℕ} (Mz Mw : Fin n → Finset (Fin n))
    (D : OrderBox (ROrderIndex n)) : Bool :=
  decide (∀ i j, i < j →
    (Mz i = {i, j} → Mz j = {i, j} → (3 : Fin 6) ∈ radiusDomainEntry D i j) ∧
    (Mw i = {i, j} → Mw j = {i, j} → (3 : Fin 6) ∈ radiusDomainEntry D i j))

theorem maximalRowCountCheck_of_covers {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (hm : AdmissibleMasses mass)
    (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀) (Mz Mw : Fin n → Finset (Fin n))
    (hz : ∀ i, MaximalTermCover (fun k t => (q t).zEquationTerm i k) (Mz i))
    (hw : ∀ i, MaximalTermCover (fun k t => (q t).wEquationTerm i k) (Mw i)) :
    maximalRowCountCheck Mz Mw = true := by
  apply decide_eq_true
  intro i
  obtain ⟨j, hij⟩ : ∃ j, i ≠ j := by
    by_cases hi : i = i₀
    · exact ⟨j₀, hi ▸ hij₀⟩
    · exact ⟨i₀, hi⟩
  have hz' := ZWSystem.z_maximalTermCover_card hm i j hij (Mz i) (hz i)
  have hw' := ZWSystem.w_maximalTermCover_card hm i j hij (Mw i) (hw i)
  constructor <;> omega

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

theorem radius_three_of_z_pair_covers (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j)
    (hi : MaximalTermCover (fun k t => (q t).zEquationTerm i k) {i, j})
    (hj : MaximalTermCover (fun k t => (q t).zEquationTerm j k) {i, j}) :
    o.radius i j = 3 :=
  (o.radius_level i j).three_iff_theta_middle.mpr
    (ZWSystem.two_z_pair_covers_radius_theta_one q hm i j hij hi hj)

theorem radius_three_of_w_pair_covers (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j)
    (hi : MaximalTermCover (fun k t => (q t).wEquationTerm i k) {i, j})
    (hj : MaximalTermCover (fun k t => (q t).wEquationTerm j k) {i, j}) :
    o.radius i j = 3 :=
  (o.radius_level i j).three_iff_theta_middle.mpr
    (ZWSystem.two_w_pair_covers_radius_theta_one q hm i j hij hi hj)

theorem maximalPairDistanceCheck_of_covers (hm : AdmissibleMasses mass)
    (Mz Mw : Fin n → Finset (Fin n)) (D : OrderBox (ROrderIndex n))
    (hD : D.Admits o.radiusCode)
    (hz : ∀ i, MaximalTermCover (fun k t => (q t).zEquationTerm i k) (Mz i))
    (hw : ∀ i, MaximalTermCover (fun k t => (q t).wEquationTerm i k) (Mw i)) :
    maximalPairDistanceCheck Mz Mw D = true := by
  apply decide_eq_true
  intro i j hij
  constructor
  · intro hi hj
    have hri := hz i
    have hrj := hz j
    rw [hi] at hri
    rw [hj] at hrj
    have hr := o.radius_three_of_z_pair_covers hm i j hij.ne hri hrj
    simpa only [hr] using o.admitted_radiusMatrix D hD i j hij.ne
  · intro hi hj
    have hri := hw i
    have hrj := hw j
    rw [hi] at hri
    rw [hj] at hrj
    have hr := o.radius_three_of_w_pair_covers hm i j hij.ne hri hrj
    simpa only [hr] using o.admitted_radiusMatrix D hD i j hij.ne

end SequenceOrderAssignment
end CentralConfigurations
