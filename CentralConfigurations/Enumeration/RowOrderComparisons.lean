import CentralConfigurations.Enumeration.OrderComparisonPrimitives
import CentralConfigurations.Enumeration.DistanceOrderDomains

/-!
# Common-row coordinate and distance comparisons

These are the calls to `CompareOrderzw` and `CompareOrderr` made by
`MaxOrderZ/W`: two off-diagonal entries in one row, or the diagonal position
followed by an off-diagonal entry. The distance diagonal denotes the constant
one, not the zero diagonal stored in the distance-order matrix.

Singleton equality uses precisely levels 1, 3, and 5. This is the mathematical
guard; Appendix II prints `Complement[...] == 0` rather than an empty list.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

noncomputable def coordinateOrderValue {n : ℕ} (x : Fin n → ℂ) (i j : Fin n) : ℂ :=
  if i = j then x i else x i - x j

theorem norm_sub_le_coordinateOrderValue {n : ℕ} (x : Fin n → ℂ) (i j : Fin n) :
    ‖x i - x j‖ ≤ ‖coordinateOrderValue x i j‖ := by
  by_cases hij : i = j
  · subst j
    simp [coordinateOrderValue]
  · simp [coordinateOrderValue, hij]

theorem coordinateOrderValue_row_triangle {n : ℕ} (x : Fin n → ℂ)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) :
    ‖coordinateOrderValue x i j‖ ≤
      ‖coordinateOrderValue x i k‖ + ‖coordinateOrderValue x j k‖ := by
  simp only [coordinateOrderValue, if_neg hij, if_neg hik]
  calc
    ‖x i - x j‖ = ‖(x i - x k) - (x j - x k)‖ := by congr 1; ring
    _ ≤ ‖x i - x k‖ + ‖x j - x k‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add le_rfl (norm_sub_le_coordinateOrderValue x j k)

theorem coordinateOrderValue_row_triangle_reverse {n : ℕ} (x : Fin n → ℂ)
    (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) :
    ‖coordinateOrderValue x i k‖ ≤
      ‖coordinateOrderValue x i j‖ + ‖coordinateOrderValue x j k‖ := by
  simp only [coordinateOrderValue, if_neg hij, if_neg hik]
  calc
    ‖x i - x k‖ = ‖(x i - x j) + (x j - x k)‖ := by congr 1; ring
    _ ≤ ‖x i - x j‖ + ‖x j - x k‖ := norm_add_le _ _
    _ ≤ _ := add_le_add le_rfl (norm_sub_le_coordinateOrderValue x j k)

def compareCoordinateRow {n : ℕ} (B : Fin n → Fin n → Finset (Fin 6))
    (i j k : Fin n) : OrderComparison :=
  let base := compareOrderDomains (B i j) (B i k)
  if base ≠ .unknown then base
  else if i ≠ j ∧ i ≠ k then
    if triangleDomainThetaCheck (B i j) (B i k) (B j k) then .equal else .unknown
  else if i = j ∧ i ≠ k then
    if triangleDomainThetaCheck (B i i) (B i k) (B k k) then .equal else .unknown
  else .unknown

theorem compareCoordinateRow_valid {n : ℕ} {s : OrderScales}
    (x : ℕ → Fin n → ℂ) (codes : Fin n → Fin n → Fin 6)
    (hlevels : ∀ i j, HasOrderLevel s (fun t => coordinateOrderValue (x t) i j) (codes i j))
    (B : Fin n → Fin n → Finset (Fin 6)) (hB : ∀ i j, codes i j ∈ B i j)
    (i j k : Fin n) :
    (compareCoordinateRow B i j k).Valid
      (fun t => coordinateOrderValue (x t) i j)
      (fun t => coordinateOrderValue (x t) i k) := by
  unfold compareCoordinateRow
  dsimp only
  split_ifs with hbase hoff ht hdiag ht
  · exact compareOrderDomains_valid (hlevels i j) (hlevels i k) _ _ (hB i j) (hB i k)
  · exact triangleDomainThetaCheck_valid (hlevels i j) (hlevels i k) (hlevels j k)
      _ _ _ (hB i j) (hB i k) (hB j k)
      (fun t => coordinateOrderValue_row_triangle (x t) i j k hoff.1 hoff.2)
      (fun t => coordinateOrderValue_row_triangle_reverse (x t) i j k hoff.1 hoff.2) ht
  · trivial
  · obtain ⟨rfl, hik⟩ := hdiag
    apply triangleDomainThetaCheck_valid (hlevels i i) (hlevels i k) (hlevels k k)
      _ _ _ (hB i i) (hB i k) (hB k k) _ _ ht
    · intro t
      simp only [coordinateOrderValue, if_neg hik]
      simpa only [sub_add_cancel] using norm_add_le (x t i - x t k) (x t k)
    · intro t
      simpa only [coordinateOrderValue, if_pos rfl, if_neg hik] using
        norm_sub_le (x t i) (x t k)
  · trivial
  · trivial

def compareOneToRadiusDomain (B : Finset (Fin 6)) : OrderComparison :=
  if 4 ≤ B.inf id then .less
  else if B.sup id ≤ 2 then .greater
  else if B = {3} then .equal
  else .unknown

theorem compareOneToRadiusDomain_valid {s : OrderScales} {f : ℕ → ℂ} {a : Fin 6}
    (hf : HasOrderLevel s f a) (B : Finset (Fin 6)) (ha : a ∈ B) :
    (compareOneToRadiusDomain B).Valid s.middle f := by
  unfold compareOneToRadiusDomain
  split_ifs with hlarge hsmall heq
  · apply hf.middle_littleO_of_three_lt
    have h := hlarge.trans (Finset.inf_le (f := id) ha)
    dsimp only [id] at h
    omega
  · apply hf.lt_three_iff_littleO_middle.mp
    have h := (Finset.le_sup (f := id) ha).trans hsmall
    dsimp only [id] at h
    omega
  · have hk : a = 3 := by simpa [heq] using ha
    exact (hf.three_iff_theta_middle.mp hk).symm
  · trivial

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

theorem compare_z_row_valid (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode)
    (i j k : Fin n) :
    (compareCoordinateRow (fun a b => B (zwOrderSlot 0 a b)) i j k).Valid
      (fun t => (q t).zOrderValue i j) (fun t => (q t).zOrderValue i k) :=
  compareCoordinateRow_valid (fun t => (q t).z) o.z o.z_level _
    (fun a b => by simpa only [orderCode_z] using hB (zwOrderSlot 0 a b)) i j k

theorem compare_w_row_valid (B : OrderBox (ZWOrderIndex n)) (hB : B.Admits o.orderCode)
    (i j k : Fin n) :
    (compareCoordinateRow (fun a b => B (zwOrderSlot 1 a b)) i j k).Valid
      (fun t => (q t).wOrderValue i j) (fun t => (q t).wOrderValue i k) :=
  compareCoordinateRow_valid (fun t => (q t).w) o.w o.w_level _
    (fun a b => by simpa only [orderCode_w] using hB (zwOrderSlot 1 a b)) i j k

theorem compare_radius_domains_valid (D : OrderBox (ROrderIndex n)) (hD : D.Admits o.radiusCode)
    (i j k m : Fin n) (hij : i ≠ j) (hkm : k ≠ m) :
    (compareOrderDomains (radiusDomainEntry D i j) (radiusDomainEntry D k m)).Valid
      (fun t => (q t).radiusOrderValue i j) (fun t => (q t).radiusOrderValue k m) :=
  compareOrderDomains_valid (o.radius_level i j) (o.radius_level k m) _ _
    (o.admitted_radiusMatrix D hD i j hij) (o.admitted_radiusMatrix D hD k m hkm)

theorem compare_one_to_radius_valid (D : OrderBox (ROrderIndex n)) (hD : D.Admits o.radiusCode)
    (i j : Fin n) (hij : i ≠ j) :
    (compareOneToRadiusDomain (radiusDomainEntry D i j)).Valid (fun _ => (1 : ℂ))
      (fun t => (q t).radiusOrderValue i j) :=
  compareOneToRadiusDomain_valid (o.radius_level i j) _ (o.admitted_radiusMatrix D hD i j hij)

end SequenceOrderAssignment
end CentralConfigurations
