import CentralConfigurations.FiveBody.OrdinaryDiagramIdentity
import CentralConfigurations.Diagrams.TriangleOrders
import CentralConfigurations.Asymptotics.OneStrokeClusterLimits
import CentralConfigurations.Enumeration.FourProductTransport

/-! Actual D7 wing and crossed separation comparisons. No reciprocal-root
mass restriction or AK order table is assumed. -/

namespace CentralConfigurations.FiveBody.Ordinary.D7
noncomputable section
open Filter Asymptotics
open scoped Topology

def zsep {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass) (i j : Fin 5) : ℕ → ℂ :=
  fun t => (q t).z i - (q t).z j
def wsep {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass) (i j : Fin 5) : ℕ → ℂ :=
  fun t => (q t).w i - (q t).w j
def radius {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass) (i j : Fin 5) : ℕ → ℂ :=
  fun t => ((q t).delta i j)⁻¹

theorem upper_support : ∀ i ∈ ({0,1,4} : Finset (Fin 5)), ∀ j ∈ ({0,1,4} : Finset (Fin 5)), i ≠ j →
    (akDiagram 6).1 (upperIndex i j) = true ∧ (akDiagram 6).2 (upperIndex i j) = false := by
  decide +kernel
theorem lower_support : ∀ i ∈ ({2,3,4} : Finset (Fin 5)), ∀ j ∈ ({2,3,4} : Finset (Fin 5)), i ≠ j →
    (akDiagram 6).2 (upperIndex i j) = true ∧ (akDiagram 6).1 (upperIndex i j) = false := by
  decide +kernel
theorem no_circles : ∀ i : Fin 5,
    (akDiagram 6).1 (upperIndex i i) = false ∧ (akDiagram 6).2 (upperIndex i i) = false := by
  decide +kernel

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
  (hd : l.diagramCode = akDiagram 6)
include hb hd

theorem upper_z_force (i j : Fin 5) (hi : i ∈ ({0,1,4} : Finset (Fin 5)))
    (hj : j ∈ ({0,1,4} : Finset (Fin 5))) (hij : i ≠ j) : l.z.force i j ≠ 0 :=
  l.z_force_ne_zero_of_code hd i j hij (upper_support i hi j hj hij).1

theorem lower_w_force (i j : Fin 5) (hi : i ∈ ({2,3,4} : Finset (Fin 5)))
    (hj : j ∈ ({2,3,4} : Finset (Fin 5))) (hij : i ≠ j) : l.w.force i j ≠ 0 :=
  l.w_force_ne_zero_of_code hd i j hij (lower_support i hi j hj hij).1

theorem upper_orders (i : Fin 5) (hi : i ∈ ({0,1} : Finset (Fin 5))) :
    zsep q i 4 =Θ[atTop] zsep q 0 1 ∧ wsep q i 4 =Θ[atTop] wsep q 0 1 := by
  have hz01 := upper_z_force l hb hd 0 1 (by decide) (by decide) (by decide)
  have hz14 := upper_z_force l hb hd 1 4 (by decide) (by decide) (by decide)
  have hz04 := upper_z_force l hb hd 0 4 (by decide) (by decide) (by decide)
  have ht := l.z_triangle_orders hb 0 1 4 (by decide) (by decide) (by decide) hz01 hz14 hz04
  have hi' : i = 0 ∨ i = 1 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hi
  rcases hi' with rfl | rfl
  · exact ⟨ht.2.1.symm, ht.2.2.2.symm⟩
  · exact ⟨ht.1.symm, ht.2.2.1.symm⟩

theorem lower_orders (i : Fin 5) (hi : i ∈ ({2,3} : Finset (Fin 5))) :
    zsep q i 4 =Θ[atTop] zsep q 2 3 ∧ wsep q i 4 =Θ[atTop] wsep q 2 3 := by
  have hw23 := lower_w_force l hb hd 2 3 (by decide) (by decide) (by decide)
  have hw34 := lower_w_force l hb hd 3 4 (by decide) (by decide) (by decide)
  have hw24 := lower_w_force l hb hd 2 4 (by decide) (by decide) (by decide)
  have ht := (l.swapBalanced hb).z_triangle_orders (fun t => (hb t).symm)
    2 3 4 (by decide) (by decide) (by decide) hw23 hw34 hw24
  have hi' : i = 2 ∨ i = 3 := by simpa only [Finset.mem_insert,Finset.mem_singleton] using hi
  rcases hi' with rfl | rfl
  · exact ⟨ht.2.2.2.symm, ht.2.1.symm⟩
  · exact ⟨ht.2.2.1.symm, ht.1.symm⟩

theorem lower_z_littleO_upper
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (i : Fin 5) (hi : i ∈ ({2,3} : Finset (Fin 5))) :
    zsep q i 4 =o[atTop] zsep q 0 1 := by
  have hi4 : i ≠ 4 := by fin_cases i <;> simp_all [Fin.ext_iff]
  have hz := upper_z_force l hb hd 0 1 (by decide) (by decide) (by decide)
  have hi' : i ∈ ({2,3,4} : Finset (Fin 5)) := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    rcases hi with h | h <;> simp [h]
  have hs := lower_support i hi' 4 (by decide) hi4
  have hlim := l.single_w_edge_z_separation_ratio_to_z_stroke_zero
    (CentralConfigurations.ScaledZWLimit.inverseScale_ne_zero (q := q) 0 1 (by decide)) i 4 0 1 hi4 (by decide) hz
    (l.z_force_zero_of_code hd i 4 hs.2) (l.w_force_ne_zero_of_code hd i 4 hi4 hs.1)
  apply (isLittleO_iff_tendsto (fun t ht => ((q t).z_separation_ne_zero (by decide : (0:Fin 5) ≠ 1) ht).elim)).mpr
  exact hlim

theorem upper_w_littleO_lower
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (i : Fin 5) (hi : i ∈ ({0,1} : Finset (Fin 5))) :
    wsep q i 4 =o[atTop] wsep q 2 3 := by
  have hi4 : i ≠ 4 := by fin_cases i <;> simp_all [Fin.ext_iff]
  have hw := lower_w_force l hb hd 2 3 (by decide) (by decide) (by decide)
  have hi' : i ∈ ({0,1,4} : Finset (Fin 5)) := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi ⊢
    rcases hi with h | h <;> simp [h]
  have hs := upper_support i hi' 4 (by decide) hi4
  have hlim := (l.swapBalanced hb).single_w_edge_z_separation_ratio_to_z_stroke_zero
    (CentralConfigurations.ScaledZWLimit.inverseScale_ne_zero
      (q := fun t => (q t).swap) 0 1 (by decide))
    i 4 2 3 hi4 (by decide) hw
    (l.w_force_zero_of_code hd i 4 hs.2) (l.z_force_ne_zero_of_code hd i 4 hi4 hs.1)
  apply (isLittleO_iff_tendsto (fun t ht => ((q t).w_separation_ne_zero (by decide : (2:Fin 5) ≠ 3) ht).elim)).mpr
  exact hlim

theorem cross_orders
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (i j : Fin 5) (hi : i ∈ ({0,1} : Finset (Fin 5)))
    (hj : j ∈ ({2,3} : Finset (Fin 5))) :
    zsep q i j =Θ[atTop] zsep q 0 1 ∧ wsep q i j =Θ[atTop] wsep q 2 3 := by
  have hu := upper_orders l hb hd i hi
  have hl := lower_orders l hb hd j hj
  have hz := hu.1.add_isLittleO (lower_z_littleO_upper l hb hd ha j hj).neg_left
  have hneg : (fun t => -wsep q j 4 t) =Θ[atTop] wsep q 2 3 :=
    ⟨hl.2.1.neg_left, hl.2.2.neg_right⟩
  have hw := (upper_w_littleO_lower l hb hd ha i hi).add_isTheta hneg
  exact ⟨⟨hz.1.congr_left (fun t => by dsimp [zsep]; ring),
    hz.2.congr_right (fun t => by dsimp [zsep]; ring)⟩,
    ⟨hw.1.congr_left (fun t => by dsimp [wsep]; ring),
    hw.2.congr_right (fun t => by dsimp [wsep]; ring)⟩⟩

end
end CentralConfigurations.FiveBody.Ordinary.D7
