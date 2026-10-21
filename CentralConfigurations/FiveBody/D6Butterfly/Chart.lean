import CentralConfigurations.FiveBody.D6Butterfly.WingLimits

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology
noncomputable section

def PairGauge.coeff {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) : Fin 8 → ℂ :=
  ![(g.normalized.z 3+g.normalized.z 4)/2/g.time,
    (g.normalized.w 0+g.normalized.w 1)/2/g.time,
    g.normalized.z 0/g.time,g.normalized.z 1/g.time,g.normalized.z 2/g.time,
    g.normalized.w 2/g.time,g.normalized.w 3/g.time,g.normalized.w 4/g.time]

def leadingZ : Fin 5 → ℂ := ![0,0,0,1,-1]
def leadingW : Fin 5 → ℂ := ![1,-1,0,0,0]
def zCoeff : Fin 5 → Fin 8 := ![2,3,4,0,0]
def wCoeff : Fin 5 → Fin 8 := ![1,1,5,6,7]

theorem PairGauge.chart {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) :
    g.normalized.z 3=1/g.time+g.time*g.coeff 0 ∧
    g.normalized.z 4= -1/g.time+g.time*g.coeff 0 ∧
    g.normalized.w 0=1/g.time+g.time*g.coeff 1 ∧
    g.normalized.w 1= -1/g.time+g.time*g.coeff 1 ∧
    g.normalized.z 0=g.time*g.coeff 2 ∧
    g.normalized.z 1=g.time*g.coeff 3 ∧
    g.normalized.z 2=g.time*g.coeff 4 ∧
    g.normalized.w 2=g.time*g.coeff 5 ∧
    g.normalized.w 3=g.time*g.coeff 6 ∧
    g.normalized.w 4=g.time*g.coeff 7 := by
  have hz := g.z_difference
  have hw := g.w_difference
  dsimp [PairGauge.coeff]
  constructor
  · field_simp [g.time_ne] at hz ⊢; linear_combination hz
  constructor
  · field_simp [g.time_ne] at hz ⊢; linear_combination -hz
  constructor
  · field_simp [g.time_ne] at hw ⊢; linear_combination hw
  constructor
  · field_simp [g.time_ne] at hw ⊢; linear_combination -hw
  field_simp [g.time_ne]
  simp

theorem PairGauge.z_coordinates {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) (i : Fin 5) :
    g.normalized.z i=leadingZ i/g.time+g.time*g.coeff (zCoeff i) := by
  obtain ⟨h3,h4,-,-,h0,h1,h2,-,-,-⟩ := g.chart
  fin_cases i <;> simp_all [leadingZ,zCoeff]

theorem PairGauge.w_coordinates {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) (i : Fin 5) :
    g.normalized.w i=leadingW i/g.time+g.time*g.coeff (wCoeff i) := by
  obtain ⟨-,-,h0,h1,-,-,-,h2,h3,h4⟩ := g.chart
  fin_cases i <;> simp_all [leadingW,wCoeff]

theorem PairGauge.scaled_z {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) (i : Fin 5) :
    g.time*g.normalized.z i=leadingZ i+g.time^2*g.coeff (zCoeff i) := by
  rw [g.z_coordinates i]; field_simp [g.time_ne]

theorem PairGauge.scaled_w {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q) (i : Fin 5) :
    g.time*g.normalized.w i=leadingW i+g.time^2*g.coeff (wCoeff i) := by
  rw [g.w_coordinates i]; field_simp [g.time_ne]

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (g : ∀ t, PairGauge (q t))
include l hm hd

theorem rotated_bigO {f : ℕ → ℂ} (hf : f =O[atTop] (fun t => (q t).inverseScale)) :
    (fun t => (g t).rotation*f t) =O[atTop] (fun t => (g t).time) ∧
    (fun t => ((g t).rotation)⁻¹*f t) =O[atTop] (fun t => (g t).time) := by
  obtain ⟨hz,hw⟩ := long_separations l hm hd
  obtain ⟨hr,hri⟩ := rotation_bounded l g hz hw
  have ht := (time_scale l g hz hw).2
  constructor
  · apply IsBigO.trans _ ht
    simpa only [one_mul] using hr.mul hf
  · apply IsBigO.trans _ ht
    simpa only [one_mul] using hri.mul hf

theorem coefficient_bounds
    (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) (i : Fin 8) :
    Bornology.IsBounded (Set.range (fun t => (g t).coeff i)) := by
  obtain ⟨hz0,hz1,hz2,hw2,hw3,hw4⟩ := short_positions l hm hd
  obtain ⟨hzs,hws⟩ := pair_sums l hm hd hb ha
  have hz (i : Fin 5) (h : (fun t => (q t).z i) =O[atTop] (fun t => (q t).inverseScale)) :
      Bornology.IsBounded (Set.range (fun t => (g t).normalized.z i/(g t).time)) :=
    bounded_range_div_of_bigO (rotated_bigO l hm hd g h).1
  have hw (i : Fin 5) (h : (fun t => (q t).w i) =O[atTop] (fun t => (q t).inverseScale)) :
      Bornology.IsBounded (Set.range (fun t => (g t).normalized.w i/(g t).time)) :=
    bounded_range_div_of_bigO (rotated_bigO l hm hd g h).2
  fin_cases i
  · have h := ((rotated_bigO l hm hd g hzs).1).const_mul_left ((2:ℂ)⁻¹)
    have he : (fun t => (2:ℂ)⁻¹*((g t).rotation*((q t).z 3+(q t).z 4))) =
        (fun t => ((g t).normalized.z 3+(g t).normalized.z 4)/2) := by
      ext t; dsimp [PairGauge.normalized,ZWSystem.rescale]; ring
    rw [he] at h
    exact bounded_range_div_of_bigO h
  · have h := ((rotated_bigO l hm hd g hws).2).const_mul_left ((2:ℂ)⁻¹)
    have he : (fun t => (2:ℂ)⁻¹*((g t).rotation⁻¹*((q t).w 0+(q t).w 1))) =
        (fun t => ((g t).normalized.w 0+(g t).normalized.w 1)/2) := by
      ext t; dsimp [PairGauge.normalized,ZWSystem.rescale]; ring
    rw [he] at h
    exact bounded_range_div_of_bigO h
  · exact hz 0 hz0
  · exact hz 1 hz1
  · exact hz 2 hz2
  · exact hw 2 hw2
  · exact hw 3 hw3
  · exact hw 4 hw4

theorem exists_chart_limits
    (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    ∃ c : Fin 8 → ℂ, ∃ u : Fin 6 → ℂ, ∃ h : Fin 4 → ℂ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ i, Tendsto (fun t => (g (φ t)).coeff i) atTop (𝓝 (c i))) ∧
      (∀ e, Tendsto (fun t => (q (φ t)).delta (wingLeft e) (wingRight e)) atTop (𝓝 (u e))) ∧
      (∀ e, u e≠0) ∧
      (∀ e, Tendsto (fun t => (q (φ t)).delta (crossLeft e) (crossRight e)/(g (φ t)).time) atTop (𝓝 (h e))) := by
  let f : ℕ → (Fin 8 ⊕ (Fin 6 ⊕ Fin 4)) → ℂ := fun t e => match e with
    | .inl i => (g t).coeff i
    | .inr (.inl i) => (q t).delta (wingLeft i) (wingRight i)
    | .inr (.inr i) => (q t).delta (crossLeft i) (crossRight i)/(g t).time
  have hB (e) : Bornology.IsBounded (Set.range (fun t => f t e)) := by
    rcases e with i | i
    · exact coefficient_bounds l hm hd g hb ha i
    rcases i with i | i
    · obtain ⟨v,-,hv⟩ := wing_cube_limits l hm hd i
      exact bounded_of_power_tendsto (by decide : 3≠0) hv
    · have ht := time_scale l g (long_separations l hm hd).1 (long_separations l hm hd).2
      exact bounded_range_div_of_bigO ((cross_delta_bigO l hm hd i).trans ht.2)
  obtain ⟨v,φ,hφ,hv⟩ := exists_finite_coordinate_limits f hB
  refine ⟨(fun i => v (.inl i)),(fun i => v (.inr (.inl i))),
    (fun i => v (.inr (.inr i))),φ,hφ,(fun i => hv (.inl i)),(fun i => hv (.inr (.inl i))),?_,
    (fun i => hv (.inr (.inr i)))⟩
  intro i hi
  change v (.inr (.inl i))=0 at hi
  obtain ⟨w,hw,hlim⟩ := wing_cube_limits l hm hd i
  have he := tendsto_nhds_unique ((hv (.inr (.inl i))).pow 3) (hlim.comp hφ.tendsto_atTop)
  rw [hi,zero_pow (by decide : 3≠0)] at he
  exact hw he.symm

end
end CentralConfigurations.FiveBody.D6
