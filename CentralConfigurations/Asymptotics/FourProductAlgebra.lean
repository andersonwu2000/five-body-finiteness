import CentralConfigurations.Asymptotics.FiniteDistanceData

/-!
# Exact algebra of the five-body four-products

The ten squared distances use the order 01,02,03,04,12,13,14,23,24,34.
For an edge e, its four-product is its squared distance times the three
squared distances of the complementary triangle. An exact monomial identity
shows that finite images of all ten four-products imply finite images of all
ten nonzero squared distances. Complex root choices remain finite choices.
-/

namespace CentralConfigurations
noncomputable section
open scoped BigOperators

def fiveBodyEdges : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def fiveBodyDisjointEdges : Fin 10 → Fin 3 → Fin 10 :=
  ![![7,8,9],![5,6,9],![4,6,8],![4,5,7],![2,3,9],
    ![1,3,8],![1,2,7],![0,3,6],![0,2,5],![0,1,4]]

def fiveBodyFourProducts {R : Type*} [CommMonoid R] (d : Fin 10 → R) (e : Fin 10) : R :=
  d e * ∏ k : Fin 3, d (fiveBodyDisjointEdges e k)

theorem five_body_edge_distinct (e : Fin 10) :
    (fiveBodyEdges e).1 ≠ (fiveBodyEdges e).2 := by
  fin_cases e <;> decide

theorem five_body_four_product_recovery {R : Type*} [CommRing R]
    (d : Fin 10 → R) (e : Fin 10) :
    d e ^ 8 * (∏ k : Fin 10, fiveBodyFourProducts d k) =
      (∏ k : Fin 3, fiveBodyFourProducts d (fiveBodyDisjointEdges e k)) ^ 4 := by
  fin_cases e <;>
    simp [fiveBodyFourProducts, fiveBodyDisjointEdges, Fin.prod_univ_succ] <;> ring

theorem five_body_four_product_ne_zero {R : Type*} [CommMonoidWithZero R]
    [NoZeroDivisors R] [Nontrivial R] (d : Fin 10 → R) (hd : ∀ e, d e ≠ 0) (e : Fin 10) :
    fiveBodyFourProducts d e ≠ 0 :=
  mul_ne_zero (hd e) (Finset.prod_ne_zero_iff.mpr (fun _ _ => hd _))

theorem finite_range_of_eighth_power {α K : Type*} [CommRing K] [IsDomain K]
    {f : α → K} (hf : (Set.range (fun a => f a ^ 8)).Finite) :
    (Set.range f).Finite := by
  apply finite_range_of_square
  apply finite_range_of_square
  apply finite_range_of_square
  simpa only [← pow_mul] using hf

theorem finite_distance_images_of_finite_four_product_images {α : Type*}
    (d : α → Fin 10 → ℂ) (hd : ∀ a e, d a e ≠ 0)
    (h : ∀ e, (Set.range (fun a => fiveBodyFourProducts (d a) e)).Finite) :
    ∀ e, (Set.range (fun a => d a e)).Finite := by
  intro e
  apply finite_range_of_eighth_power
  have hall := finite_range_functions h
  have hr := finite_range_apply hall (fun p : Fin 10 → ℂ =>
    (∏ k : Fin 3, p (fiveBodyDisjointEdges e k)) ^ 4 / ∏ k : Fin 10, p k)
  convert hr using 2
  funext a
  apply (eq_div_iff (Finset.prod_ne_zero_iff.mpr (fun k _ =>
    five_body_four_product_ne_zero (d a) (hd a) k))).mpr
  exact five_body_four_product_recovery (d a) e

end
end CentralConfigurations
