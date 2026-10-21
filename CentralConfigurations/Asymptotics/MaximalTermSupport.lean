import CentralConfigurations.Asymptotics.PairEstimates
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
# Candidate maximal terms in a finite balanced row

Proposition 4.13 uses a candidate set formed by deleting terms for which a
sound strict comparison has been established. The vector norm proves that
such a set has at least two elements. No total growth ordering, convergent
ratio extraction, or power-law model inside an open level is required.
-/

namespace CentralConfigurations

open scoped BigOperators Topology
open Filter Asymptotics

/-- Every omitted term is certified smaller than some term in the full row.
The dominating term need not itself be retained. -/
def MaximalTermCover {ι : Type*} [Fintype ι] (f : ι → ℕ → ℂ) (M : Finset ι) : Prop :=
  ∀ i, i ∉ M → ∃ j, f i =o[atTop] f j

theorem MaximalTermCover.comp {ι : Type*} [Fintype ι]
    {f : ι → ℕ → ℂ} {M : Finset ι} (h : MaximalTermCover f M)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) :
    MaximalTermCover (fun i => f i ∘ φ) M := by
  intro i hi
  obtain ⟨j, hj⟩ := h i hi
  exact ⟨j, hj.comp_tendsto hφ⟩

theorem MaximalTermCover.mono {ι : Type*} [Fintype ι]
    {f : ι → ℕ → ℂ} {M N : Finset ι} (h : MaximalTermCover f M) (hMN : M ⊆ N) :
    MaximalTermCover f N := fun i hi => h i (fun him => hi (hMN him))

theorem term_isBigO_vector {ι : Type*} [Fintype ι] (f : ι → ℕ → ℂ) (i : ι) :
    f i =O[atTop] (fun t j => f j t) := by
  apply IsBigO.of_bound 1
  filter_upwards with t
  simpa only [one_mul] using norm_le_pi_norm (fun j => f j t) i

theorem MaximalTermCover.omitted_littleO_vector {ι : Type*} [Fintype ι]
    {f : ι → ℕ → ℂ} {M : Finset ι} (h : MaximalTermCover f M)
    (i : ι) (hi : i ∉ M) : f i =o[atTop] (fun t j => f j t) := by
  obtain ⟨j, hj⟩ := h i hi
  exact hj.trans_isBigO (term_isBigO_vector f j)

theorem not_all_terms_littleO_vector {ι : Type*} [Fintype ι]
    (f : ι → ℕ → ℂ) (hzero : ∃ i, ∀ t, f i t ≠ 0)
    (hsmall : ∀ i, f i =o[atTop] (fun t j => f j t)) : False := by
  obtain ⟨i, hi⟩ := hzero
  have hv : ∀ t, (fun j => f j t) ≠ 0 := by
    intro t he
    exact hi t (congrFun he i)
  exact isLittleO_irrefl (Eventually.of_forall hv).frequently (isLittleO_pi.mpr hsmall)

theorem MaximalTermCover.two_le_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℕ → ℂ} {M : Finset ι} (h : MaximalTermCover f M)
    (hzero : ∃ i, ∀ t, f i t ≠ 0) (hsum : ∀ t, ∑ i, f i t = 0) : 2 ≤ M.card := by
  by_contra hn
  have hc : M.card = 0 ∨ M.card = 1 := by omega
  rcases hc with hc | hc
  · have he := Finset.card_eq_zero.mp hc
    exact not_all_terms_littleO_vector f hzero (fun i =>
      h.omitted_littleO_vector i (by simp [he]))
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    have hrest : (fun t => ∑ j ∈ Finset.univ.erase i, f j t) =o[atTop]
        (fun t j => f j t) := by
      apply IsLittleO.sum
      intro j hj
      exact h.omitted_littleO_vector j (by simpa [hi] using (Finset.mem_erase.mp hj).1)
    have hsingle : f i =o[atTop] (fun t j => f j t) := hrest.neg_left.congr_left (by
      intro t
      have he := Finset.sum_erase_add (s := Finset.univ) (f := fun j => f j t)
        (Finset.mem_univ i)
      rw [hsum t] at he
      linear_combination -he)
    apply not_all_terms_littleO_vector f hzero
    intro j
    by_cases hji : j = i
    · simpa only [hji] using hsingle
    · exact h.omitted_littleO_vector j (by simpa [hi] using hji)

/-- With only two candidate terms, the whole balanced row is bounded by
either candidate, even if the preliminary comparisons were incomplete. -/
theorem MaximalTermCover.vector_isBigO_of_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℕ → ℂ} {i j : ι} (h : MaximalTermCover f {i, j}) (hij : i ≠ j)
    (hsum : ∀ t, ∑ k, f k t = 0) : (fun t k => f k t) =O[atTop] f j := by
  have hrest : (fun t => ∑ k ∈ (Finset.univ.erase i).erase j, f k t) =o[atTop]
      (fun t k => f k t) := by
    apply IsLittleO.sum
    intro k hk
    have hk' := Finset.mem_erase.mp hk
    have hki := (Finset.mem_erase.mp hk'.2).1
    exact h.omitted_littleO_vector k (by simp [hki, hk'.1])
  have hp : (fun t => f i t + f j t) =o[atTop] (fun t k => f k t) :=
    hrest.neg_left.congr_left (by
      intro t
      have he₁ := Finset.sum_erase_add (s := Finset.univ) (f := fun k => f k t)
        (Finset.mem_univ i)
      have he₂ := Finset.sum_erase_add (s := Finset.univ.erase i) (f := fun k => f k t)
        (by simp [hij.symm] : j ∈ Finset.univ.erase i)
      rw [hsum t] at he₁
      linear_combination -he₁ - he₂)
  let b : ℕ → ι → ℂ := fun t k => if k = i then -(f j t) else if k = j then f j t else 0
  have he : (fun t k => f k t - b t k) =o[atTop] (fun t k => f k t) := by
    apply isLittleO_pi.mpr
    intro k
    by_cases hki : k = i
    · subst k
      simpa [b] using hp
    · by_cases hkj : k = j
      · subst k
        simpa [b, hki] using (isLittleO_zero (fun t k => f k t) atTop)
      · simpa [b, hki, hkj] using h.omitted_littleO_vector k (by simp [hki, hkj])
  have hb : (fun t k => f k t) =O[atTop] b :=
    he.neg_left.right_isBigO_add.congr_right (by intro t; ext k; simp)
  apply hb.trans
  apply isBigO_pi.mpr
  intro k
  by_cases hki : k = i
  · simpa [b, hki] using (isBigO_refl (f j) atTop).neg_left
  · by_cases hkj : k = j
    · simpa [b, hki, hkj, hij.symm] using (isBigO_refl (f j) atTop)
    · simpa [b, hki, hkj] using (isBigO_zero (f j) atTop)

theorem MaximalTermCover.omitted_littleO_of_pair {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℕ → ℂ} {i j : ι} (h : MaximalTermCover f {i, j}) (hij : i ≠ j)
    (hsum : ∀ t, ∑ k, f k t = 0) (k : ι) (hk : k ∉ ({i, j} : Finset ι)) :
    f k =o[atTop] f j :=
  (h.omitted_littleO_vector k hk).trans_isBigO (h.vector_isBigO_of_pair hij hsum)

theorem MaximalTermCover.pair_isTheta {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → ℕ → ℂ} {i j : ι} (h : MaximalTermCover f {i, j}) (hij : i ≠ j)
    (hsum : ∀ t, ∑ k, f k t = 0) : f i =Θ[atTop] f j := by
  have hswap : MaximalTermCover f {j, i} := by simpa only [Finset.pair_comm] using h
  exact ⟨(term_isBigO_vector f i).trans (h.vector_isBigO_of_pair hij hsum),
    (term_isBigO_vector f j).trans (hswap.vector_isBigO_of_pair hij.symm hsum)⟩

namespace ZWSystem

variable {n : ℕ} {mass : Fin n → ℂ}

def zEquationTerm (q : ZWSystem ℂ n mass) (i j : Fin n) : ℂ :=
  if j = i then -q.z i else mass j * q.zForce i j

def wEquationTerm (q : ZWSystem ℂ n mass) (i j : Fin n) : ℂ :=
  if j = i then -q.w i else mass j * q.wForce i j

theorem zEquationTerm_sum (q : ZWSystem ℂ n mass) (i : Fin n) :
    ∑ j, q.zEquationTerm i j = 0 := by
  have he (j : Fin n) : q.zEquationTerm i j =
      mass j * q.zForce i j - if j = i then q.z i else 0 := by
    by_cases hji : j = i
    · subst j
      simp [zEquationTerm, zForce]
    · simp [zEquationTerm, hji]
  simp_rw [he]
  rw [Finset.sum_sub_distrib]
  have hf : (∑ j, mass j * q.zForce i j) = q.z i := by
    simpa only [zForce, mul_assoc] using (q.force_z i).symm
  simp [hf]

theorem wEquationTerm_sum (q : ZWSystem ℂ n mass) (i : Fin n) :
    ∑ j, q.wEquationTerm i j = 0 := q.swap.zEquationTerm_sum i

theorem zForce_ne_zero_of_ne (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) :
    q.zForce i j ≠ 0 := by
  have hd : q.delta i j ≠ 0 := by
    intro h
    have he := q.distance i j hij
    simp [h] at he
  exact mul_ne_zero (pow_ne_zero 3 hd) (q.z_separation_ne_zero hij)

theorem wForce_ne_zero_of_ne (q : ZWSystem ℂ n mass) (i j : Fin n) (hij : i ≠ j) :
    q.wForce i j ≠ 0 := q.swap.zForce_ne_zero_of_ne i j hij

theorem zEquationTerm_nonzero (q : ZWSystem ℂ n mass) (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j) : q.zEquationTerm i j ≠ 0 := by
  simp only [zEquationTerm, if_neg hij.symm]
  have hmj : mass j ≠ 0 := by simpa using hm {j} (Finset.singleton_nonempty j)
  exact mul_ne_zero hmj (q.zForce_ne_zero_of_ne i j hij)

theorem wEquationTerm_nonzero (q : ZWSystem ℂ n mass) (hm : AdmissibleMasses mass)
    (i j : Fin n) (hij : i ≠ j) : q.wEquationTerm i j ≠ 0 :=
  q.swap.zEquationTerm_nonzero hm i j hij

theorem z_maximalTermCover_card {q : ℕ → ZWSystem ℂ n mass}
    (hm : AdmissibleMasses mass) (i j : Fin n) (hij : i ≠ j) (M : Finset (Fin n))
    (hM : MaximalTermCover (fun k t => (q t).zEquationTerm i k) M) : 2 ≤ M.card :=
  hM.two_le_card ⟨j, fun t => (q t).zEquationTerm_nonzero hm i j hij⟩
    (fun t => (q t).zEquationTerm_sum i)

theorem w_maximalTermCover_card {q : ℕ → ZWSystem ℂ n mass}
    (hm : AdmissibleMasses mass) (i j : Fin n) (hij : i ≠ j) (M : Finset (Fin n))
    (hM : MaximalTermCover (fun k t => (q t).wEquationTerm i k) M) : 2 ≤ M.card :=
  z_maximalTermCover_card (q := fun t => (q t).swap) hm i j hij M hM

end ZWSystem
end CentralConfigurations
