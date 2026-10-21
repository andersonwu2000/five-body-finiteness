import CentralConfigurations.Enumeration.SequenceOrderDomains
import CentralConfigurations.Enumeration.DistanceTables

/-!
# Corollary 4.3: z/w covering families produce distance covering families

Distance domains store strict upper-triangular entries; decoding supplies
symmetry and empty diagonal entries. The coverage theorem quantifies over
every subsequence with fixed distance levels, even when its z/w levels have
not yet been fixed. A further extraction preserves the original distance code.
-/

namespace CentralConfigurations

open scoped Topology
open Filter

abbrev ROrderIndex (n : ℕ) := StrictUpperIndex n

def radiusDomainEntry {n : ℕ} (D : OrderBox (ROrderIndex n)) (i j : Fin n) : Finset (Fin 6) :=
  if hij : i < j then D ⟨(i, j), hij⟩
  else if hji : j < i then D ⟨(j, i), hji⟩
  else ∅

@[simp] theorem radiusDomainEntry_diagonal {n : ℕ} (D : OrderBox (ROrderIndex n)) (i : Fin n) :
    radiusDomainEntry D i i = ∅ := by simp [radiusDomainEntry]

theorem radiusDomainEntry_symm {n : ℕ} (D : OrderBox (ROrderIndex n)) (i j : Fin n) :
    radiusDomainEntry D i j = radiusDomainEntry D j i := by
  rcases lt_trichotomy i j with hij | hij | hji
  · simp [radiusDomainEntry, hij, not_lt_of_ge hij.le]
  · subst j; rfl
  · simp [radiusDomainEntry, hji, not_lt_of_ge hji.le]

def producedDistanceBox {n : ℕ} (d : DiagramCode n) (B : OrderBox (ZWOrderIndex n)) :
    OrderBox (ROrderIndex n) := fun p =>
  (B (zwOrderSlot 0 p.1.1 p.1.2)).biUnion fun z =>
    (B (zwOrderSlot 1 p.1.1 p.1.2)).biUnion fun w =>
      distanceOrderTable (d.1 (upperIndex p.1.1 p.1.2) || d.2 (upperIndex p.1.1 p.1.2)) z w

def producedDistanceFamily {n : ℕ} (d : DiagramCode n)
    (C : Finset (OrderBox (ZWOrderIndex n))) : Finset (OrderBox (ROrderIndex n)) :=
  C.image (producedDistanceBox d)

theorem producedDistanceBox_excludes_zero {n : ℕ} (d : DiagramCode n)
    (B : OrderBox (ZWOrderIndex n)) (p : ROrderIndex n) :
    (0 : Fin 6) ∉ producedDistanceBox d B p := by
  intro h
  obtain ⟨z, _, h⟩ := Finset.mem_biUnion.mp h
  obtain ⟨w, _, h⟩ := Finset.mem_biUnion.mp h
  exact zero_not_mem_distanceOrderTable _ z w h

def HasRadiusOrderCode {n : ℕ} {mass : Fin n → ℂ} (q : ℕ → ZWSystem ℂ n mass)
    (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (r : ROrderIndex n → Fin 6) : Prop :=
  ∀ p, HasOrderLevel (ZWSystem.orderDistanceScales q i₀ j₀ hij₀ ha)
    (fun t => (q t).radiusOrderValue p.1.1 p.1.2) (r p)

theorem HasRadiusOrderCode.comp {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
    {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {r : ROrderIndex n → Fin 6} (h : HasRadiusOrderCode q i₀ j₀ hij₀ ha r)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) :
    HasRadiusOrderCode (q ∘ φ) i₀ j₀ hij₀ (ha.comp hφ.tendsto_atTop) r :=
  fun p => (h p).comp φ hφ.tendsto_atTop

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

def radiusCode : ROrderIndex n → Fin 6 := fun p => o.radius p.1.1 p.1.2

theorem hasRadiusOrderCode : HasRadiusOrderCode q i₀ j₀ hij₀ ha o.radiusCode :=
  fun p => o.radius_level p.1.1 p.1.2

theorem admitted_radiusMatrix (D : OrderBox (ROrderIndex n)) (hD : D.Admits o.radiusCode)
    (i j : Fin n) (hij : i ≠ j) : o.radius i j ∈ radiusDomainEntry D i j := by
  rcases lt_trichotomy i j with hij' | hij' | hji
  · simpa only [radiusDomainEntry, dif_pos hij', radiusCode] using hD ⟨(i, j), hij'⟩
  · exact (hij hij').elim
  · have h := hD ⟨(j, i), hji⟩
    rw [o.radius_symm i j]
    simpa only [radiusDomainEntry, dif_neg (not_lt_of_ge hji.le), dif_pos hji, radiusCode] using h

variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
include hb

theorem mem_distanceOrderTable_matrix (i j : Fin n) (hij : i ≠ j) :
    o.radius i j ∈ distanceOrderTable
      (decide (l.z.matrix i j = 1) || decide (l.w.matrix i j = 1)) (o.z i j) (o.w i j) := by
  by_cases hz : l.z.force i j = 0
  · by_cases hw : l.w.force i j = 0
    · simpa [distanceOrderTable, OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw]
        using o.mem_absentDistanceTable l hb i j hij hz hw
    · simpa [distanceOrderTable, OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw]
        using o.mem_edgeDistanceTable l hb i j hij (Or.inr hw)
  · by_cases hw : l.w.force i j = 0
    · simpa [distanceOrderTable, OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw]
        using o.mem_edgeDistanceTable l hb i j hij (Or.inl hz)
    · simpa [distanceOrderTable, OneColorLimit.matrix, OneColorLimit.Incident, hij, hz, hw]
        using o.mem_edgeDistanceTable l hb i j hij (Or.inl hz)

theorem admitted_producedDistanceBox (B : OrderBox (ZWOrderIndex n))
    (hB : B.Admits o.orderCode) : (producedDistanceBox l.diagramCode B).Admits o.radiusCode := by
  rintro ⟨⟨i, j⟩, hij⟩
  apply Finset.mem_biUnion.mpr
  refine ⟨o.z i j, ?_, Finset.mem_biUnion.mpr ⟨o.w i j, ?_, ?_⟩⟩
  · simpa only [orderCode_z] using hB (zwOrderSlot 0 i j)
  · simpa only [orderCode_w] using hB (zwOrderSlot 1 i j)
  · simpa only [ScaledZWLimit.diagramCode, BinaryMatrixCode.encode, upperIndex,
      min_eq_left hij.le, max_eq_right hij.le, radiusCode]
      using o.mem_distanceOrderTable_matrix l hb i j hij.ne

end SequenceOrderAssignment

theorem HasRadiusOrderCode.eq_radiusCode {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {r : ROrderIndex n → Fin 6} (h : HasRadiusOrderCode q i₀ j₀ hij₀ ha r)
    (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha) : r = o.radiusCode := by
  funext p
  exact (h p).unique (o.hasRadiusOrderCode p)

/-- The r-order coverage quantifier from Definition 4.2. -/
def ROrderCoverage {n : ℕ} {mass : Fin n → ℂ} (q : ℕ → ZWSystem ℂ n mass)
    (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (D : Finset (OrderBox (ROrderIndex n))) : Prop :=
  ∀ (φ : ℕ → ℕ) (hφ : StrictMono φ) (r : ROrderIndex n → Fin 6),
    HasRadiusOrderCode (q ∘ φ) i₀ j₀ hij₀ (ha.comp hφ.tendsto_atTop) r →
      OrderBox.CoveredBy D r

/-- Corollary 4.3, for a general covering family; a singleton is the printed
single-matrix statement. No fixed z/w levels are assumed of the input subsequence. -/
theorem ZWOrderCoverage.producedDistances {n : ℕ} {mass : Fin n → ℂ}
    {q : ℕ → ZWSystem ℂ n mass} {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
    {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
    {C : Finset (OrderBox (ZWOrderIndex n))} (hC : ZWOrderCoverage q i₀ j₀ hij₀ ha C)
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) :
    ROrderCoverage q i₀ j₀ hij₀ ha (producedDistanceFamily l.diagramCode C) := by
  intro φ hφ r hr
  obtain ⟨ψ, hψ, ⟨o⟩⟩ := exists_sequenceOrderAssignment (q ∘ φ)
    (fun t => hb (φ t)) i₀ j₀ hij₀ (ha.comp hφ.tendsto_atTop)
  rw [(hr.comp ψ hψ).eq_radiusCode o]
  obtain ⟨B, hB, ho⟩ := hC (φ ∘ ψ) (hφ.comp hψ) o.orderCode o.hasZWOrderCode
  exact ⟨producedDistanceBox l.diagramCode B, Finset.mem_image.mpr ⟨B, hB, rfl⟩,
    o.admitted_producedDistanceBox (l.comp (φ ∘ ψ) (hφ.comp hψ).tendsto_atTop)
      (fun t => hb (φ (ψ t))) B ho⟩

theorem not_empty_radius_coverage {n : ℕ} {mass : Fin n → ℂ}
    (q : ℕ → ZWSystem ℂ n mass) (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖) :
    ¬ ROrderCoverage q i₀ j₀ hij₀ ha ∅ := by
  intro hc
  obtain ⟨φ, hφ, ⟨o⟩⟩ := exists_sequenceOrderAssignment q hb i₀ j₀ hij₀ ha
  obtain ⟨D, hD, _⟩ := hc φ hφ o.radiusCode o.hasRadiusOrderCode
  exact Finset.notMem_empty _ hD

end CentralConfigurations
