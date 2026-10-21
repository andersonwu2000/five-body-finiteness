import CentralConfigurations.Asymptotics.PairTorque

/-!
# The cubic-mass obstruction for the second trace-two rule

Chang (2023), Theorem 3.3(d), using the torque argument of Albouy--Kaloshin
(2012), Proposition 4. All asymptotic inputs below are derived from the same
actual balanced sequence. The ratio is not an independently chosen root.
-/

namespace CentralConfigurations

open Filter Asymptotics
open scoped Topology BigOperators

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))

theorem trace_two_exterior_positions_zero (i j : Fin n) (hij : i ≠ j)
    (ht : (∑ a, l.z.matrix a a) = 2) (hi : l.z.matrix i i = 1)
    (hj : l.z.matrix j j = 1) :
    ∀ r, r ≠ i → r ≠ j → l.z.position r = 0 := by
  intro r hri hrj
  have hr := two_diagonals_exhaust l.z.matrix i j r hij hri hrj ht hi hj
  simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hr

theorem isolated_pair_leading_balance (i j : Fin n) (hij : i ≠ j)
    (he : ∀ r, r ≠ i → r ≠ j → l.z.force i r = 0 ∧ l.z.force j r = 0) :
    mass i * l.z.position i + mass j * l.z.position j = 0 := by
  have h := l.z.component_balance {i, j} (by
    intro a ha r hr
    have hr' : r ≠ i ∧ r ≠ j := by simpa using hr
    rcases (show a = i ∨ a = j by simpa using ha) with h | h
    · subst a
      exact (he r hr'.1 hr'.2).1
    · subst a
      exact (he r hr'.1 hr'.2).2)
  simpa only [Finset.sum_pair hij] using h

/-- If exactly one exterior body is uncircled in w, torque forces the excluded
cubic mass relation. The exterior may have additional nonmaximal z-strokes. -/
theorem trace_two_single_exterior_cubic
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hm : AdmissibleMasses mass) (i j k : Fin n)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (ht : (∑ a, l.z.matrix a a) = 2) (hi : l.z.matrix i i = 1)
    (hj : l.z.matrix j j = 1)
    (he : ∀ r, r ≠ i → r ≠ j → l.z.force i r = 0 ∧ l.z.force j r = 0)
    (hwk : l.w.position k = 0)
    (hwrest : ∀ r, r ≠ i → r ≠ j → r ≠ k → l.w.position r ≠ 0) :
    mass i ^ 3 + mass j ^ 3 = 0 := by
  classical
  have hp := l.trace_two_positions hm hij ht hi hj
  have hpi : l.z.position i ≠ 0 := by simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hi
  have hpj : l.z.position j ≠ 0 := by simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hj
  have hz0 := l.trace_two_exterior_positions_zero i j hij ht hi hj
  have hwi := l.w_position_small_of_unique_z_position hb i hp.2.1
  have hwj := l.w_position_small_of_unique_z_position hb j hp.2.2
  have hrows := l.trace_two_companion_rows_zero ha hm i j hij ht hi hj
  have hwi0 : l.w.position i = 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident] using (hrows i).1
  have hwj0 : l.w.position j = 0 := by
    simpa [OneColorLimit.matrix, OneColorLimit.Incident] using (hrows j).2
  have hci (r : Fin n) (hri : r ≠ i) (hrj : r ≠ j) :
      Tendsto (fun t => (q t).torqueCorrection i r) atTop (𝓝 (-1)) :=
    l.torqueCorrection_limit hb i r hri.symm hpi (hz0 r hri hrj) hwi (he r hri hrj).1
  have hcj (r : Fin n) (hri : r ≠ i) (hrj : r ≠ j) :
      Tendsto (fun t => (q t).torqueCorrection j r) atTop (𝓝 (-1)) :=
    l.torqueCorrection_limit hb j r hrj.symm hpj (hz0 r hri hrj) hwj (he r hri hrj).2
  have hdi (r : Fin n) (hri : r ≠ i) (hrj : r ≠ j) (hrk : r ≠ k) :
      Tendsto (fun t => (q t).delta i r / (q t).delta i k) atTop (𝓝 0) :=
    l.delta_ratio_limit_zero hb i r i k hri.symm hik (hp.2.1 r hri)
      (by rw [hwi0]; exact (hwrest r hri hrj hrk).symm) (hwi0.trans hwk.symm)
  have hdj (r : Fin n) (hri : r ≠ i) (hrj : r ≠ j) (hrk : r ≠ k) :
      Tendsto (fun t => (q t).delta j r / (q t).delta i k) atTop (𝓝 0) :=
    l.delta_ratio_limit_zero hb j r i k hrj.symm hik (hp.2.2 r hrj)
      (by rw [hwj0]; exact (hwrest r hri hrj hrk).symm) (hwi0.trans hwk.symm)
  have hmj : mass j ≠ 0 := by simpa using hm {j} (by simp)
  have hmk : mass k ≠ 0 := by simpa using hm {k} (by simp)
  have hratio := pair_torque_ratio_limit q i j k hij hik hjk hmj hmk hci hcj hdi hdj
  have hzr := l.z_separation_ratio_limit i k j k hik (hp.2.2 k hjk.symm)
  rw [hz0 k hik.symm hjk.symm, sub_zero, sub_zero] at hzr
  have hwr := l.w_separation_ratio_one_of_small hb i j k hjk hwi hwj
    (he k hik.symm hjk.symm).2
  have hsquare : Tendsto (fun t => ((q t).delta j k / (q t).delta i k) ^ 2)
      atTop (𝓝 (l.z.position i / l.z.position j)) := by
    have hh := hzr.mul hwr
    simp only [mul_one] at hh
    convert hh using 1
    funext t
    have hid := (ZWSystem.pairEstimateData q hb j k hjk).delta_ratio_square
      (ZWSystem.pairEstimateData q hb i k hik) t
    change ((q t).delta j k / (q t).delta i k) ^ 2 =
      (((q t).z i - (q t).z k) * ((q t).w i - (q t).w k)) /
        (((q t).z j - (q t).z k) * ((q t).w j - (q t).w k)) at hid
    rw [hid]
    simp only [div_eq_mul_inv, mul_inv]
    ring
  have hlim := tendsto_nhds_unique (hratio.pow 2) hsquare
  have heq : mass i ^ 2 * l.z.position j = l.z.position i * mass j ^ 2 := by
    field_simp [hmj, hpj] at hlim
    linear_combination hlim
  have hbal := l.isolated_pair_leading_balance i j hij he
  have hc : (mass i ^ 3 + mass j ^ 3) * l.z.position j = 0 := by
    linear_combination mass j ^ 2 * hbal + mass i * heq
  exact (mul_eq_zero.mp hc).resolve_right hpj

end ScaledZWLimit

/-- A binary diagonal of trace n-3 has exactly one zero outside two prescribed
zero entries. This is a finite counting statement, not an enumeration oracle. -/
theorem trace_defect_three_exterior {n : ℕ} (B : Fin n → Fin n → ℕ)
    (hn : 3 ≤ n) (hb : ∀ r, B r r = 0 ∨ B r r = 1)
    (i j : Fin n) (hij : i ≠ j) (hi : B i i = 0) (hj : B j j = 0)
    (ht : (∑ r, B r r) = n - 3) :
    ∃ k, k ≠ i ∧ k ≠ j ∧ B k k = 0 ∧
      ∀ r, r ≠ i → r ≠ j → r ≠ k → B r r ≠ 0 := by
  classical
  let c := Finset.univ.filter (fun r => B r r = 0)
  have hcount : (∑ r : Fin n, if B r r = 0 then (1 : ℕ) else 0) = c.card := by
    simp only [c, Finset.sum_boole, Nat.cast_id]
  have htotal : c.card + (∑ r, B r r) = n := by
    rw [← hcount, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _r : Fin n, (1 : ℕ) := by
        apply Finset.sum_congr rfl
        intro r _
        rcases hb r with h | h <;> simp [h]
      _ = n := by simp
  have hc : c.card = 3 := by omega
  have hic : i ∈ c := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
  have hjc : j ∈ c.erase i := Finset.mem_erase.mpr
    ⟨hij.symm, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
  have hc' : ((c.erase i).erase j).card = 1 := by
    rw [Finset.card_erase_of_mem hjc, Finset.card_erase_of_mem hic, hc]
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hc'
  have hk' : k ∈ (c.erase i).erase j := by rw [hk]; simp
  have hkj := (Finset.mem_erase.mp hk').1
  have hkci := (Finset.mem_erase.mp hk').2
  have hki := (Finset.mem_erase.mp hkci).1
  have hkc := (Finset.mem_erase.mp hkci).2
  refine ⟨k, hki, hkj, (Finset.mem_filter.mp hkc).2, ?_⟩
  intro r hri hrj hrk hr0
  have hr : r ∈ (c.erase i).erase j := Finset.mem_erase.mpr ⟨hrj,
    Finset.mem_erase.mpr ⟨hri, Finset.mem_filter.mpr ⟨Finset.mem_univ r, hr0⟩⟩⟩
  rw [hk] at hr
  exact hrk (Finset.mem_singleton.mp hr)

def TraceTwoCubicRule {n : ℕ} (mass : Fin n → ℂ) (A B : Fin n → Fin n → ℕ) : Prop :=
  ∀ i j, i ≠ j → (∑ a, A a a) = 2 → A i i = 1 → A j j = 1 →
    (∀ r, r ≠ i → r ≠ j → A i r = 0 ∧ A j r = 0) →
    mass i ^ 3 + mass j ^ 3 ≠ 0 → (∑ r, B r r) ≠ n - 3

/-- The remaining conclusion of Theorem 3.3(d), derived from an actual nonzero
two-color limit. Isolation of the pair suffices; other exterior strokes are allowed. -/
theorem ScaledZWLimit.trace_two_cubic_rule {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hm : AdmissibleMasses mass) (hw : l.w.Nonzero) :
    TraceTwoCubicRule mass l.z.matrix l.w.matrix := by
  classical
  intro i j hij ht hi hj he hmc htrace
  have hrows := l.trace_two_companion_rows_zero ha hm i j hij ht hi hj
  have hn : 3 ≤ n := by
    obtain ⟨u, v, huv, hf⟩ := hw.exists_stroke
    have huv' : l.w.matrix u v = 1 := by
      simp [OneColorLimit.matrix, OneColorLimit.Incident, huv, hf]
    have hui : u ≠ i := by
      intro hu
      subst u
      have := (hrows v).1
      omega
    have huj : u ≠ j := by
      intro hu
      subst u
      have := (hrows v).2
      omega
    have hcard := Finset.card_le_card (Finset.subset_univ ({i, j, u} : Finset (Fin n)))
    simpa [hij, Ne.symm hui, Ne.symm huj] using hcard
  obtain ⟨k, hki, hkj, hk, hrest⟩ := trace_defect_three_exterior l.w.matrix hn
    (fun r => l.w.matrix_binary r r) i j hij (hrows i).1 (hrows j).2 htrace
  apply hmc
  apply l.trace_two_single_exterior_cubic hb ha hm i j k hij hki.symm hkj.symm ht hi hj
  · intro r hri hrj
    simpa [OneColorLimit.matrix, OneColorLimit.Incident, Ne.symm hri, Ne.symm hrj]
      using he r hri hrj
  · simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hk
  · intro r hri hrj hrk
    simpa [OneColorLimit.matrix, OneColorLimit.Incident] using hrest r hri hrj hrk

end CentralConfigurations
