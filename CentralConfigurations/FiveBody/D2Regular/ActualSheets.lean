import CentralConfigurations.FiveBody.D2Regular.BaseResidual

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter
open scoped Topology
set_option maxHeartbeats 2000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

theorem actual_modelZeta (t : ℕ) (p : Fin 2) (i : Fin 3) :
    modelZeta s (e.chart hm t).time (actualCoordinates s e hm t) p i=(e.chart hm t).zeta p i := by
  dsimp only [modelZeta]
  rw [actual_modelC]
  rfl

theorem actual_modelChi (t : ℕ) (p : Fin 2) (i : Fin 3) :
    modelChi s (e.chart hm t).time (actualCoordinates s e hm t) p i=(e.chart hm t).chi p i := by
  dsimp only [modelChi]
  rw [actual_modelD]
  rfl

theorem actual_pair_sheet : ∀ᶠ t in atTop,
    (e.chart hm t).point.delta 3 4=modelPairRoot s e (actualCoordinates s e hm t) := by
  have hr : s.pairDelta≠0 := by
    intro hh
    have he := e.pair_leading_metric hm
    simp [hh] at he
  have hmetric (t : ℕ) : (e.chart hm t).point.delta 3 4^2*
      (pairMass (fun i => (m i:ℂ))^2*(e.chart hm t).beta)=1 := by
    simpa only [mul_assoc] using (e.chart hm t).pair_metric
  exact actual_root_eventually_sheet hr (pair_base_product_ne s e hm) hmetric
    (e.pair_delta_limit hm) ((e.beta_limit hm).const_mul (pairMass (fun i => (m i:ℂ))^2))

theorem actual_triangle_sheet (i j : Fin 3) : ∀ᶠ t in atTop,
    (e.chart hm t).point.delta (tripleIndex i) (tripleIndex j)=
      modelTriangleRoot s (actualCoordinates s e hm t) i j := by
  by_cases hij : i=j
  · subst j
    exact Filter.Eventually.of_forall (fun t => by simp [modelTriangleRoot,(e.chart hm t).point.delta_diagonal])
  · have hc (k : Fin 3) : Tendsto (fun t => (e.chart hm t).c k) atTop (𝓝 ((normalizedTriangle s).z k)) :=
      e.c_limit hm k
    have hd (k : Fin 3) : Tendsto (fun t => (e.chart hm t).d k) atTop (𝓝 (leadingD s k)) := by
      simpa [leadingD,normalizedTriangle,ZWSystem.rescale,div_eq_mul_inv,mul_comm] using e.d_limit hm k
    have hh := actual_root_eventually_sheet (s.triangle.delta_ne_zero i j hij)
      (triangle_base_product_ne s i j hij) (fun t => (e.chart hm t).internal_metric i j hij)
      (e.triangle_delta_limit hm i j) (((hc i).sub (hc j)).mul ((hd i).sub (hd j)))
    filter_upwards [hh] with t ht
    rw [modelTriangleRoot,if_neg hij,actual_modelC,actual_modelC,actual_modelD,actual_modelD]
    exact ht

theorem actual_cross_sheet (p : Fin 2) (i : Fin 3) : ∀ᶠ t in atTop,
    (e.chart hm t).cross p i=modelCrossRoot s e (e.chart hm t).time (actualCoordinates s e hm t) p i := by
  have hr : s.cross p i/e.ratio≠0 := by
    intro hh
    have he := cross_base_metric s e hm p i
    simp [hh] at he
  have hmetric (t : ℕ) : (e.chart hm t).cross p i^2*
      ((e.chart hm t).zeta p i*(e.chart hm t).chi p i)=1 := by
    simpa only [mul_assoc] using (e.chart hm t).cross_metric p i
  have hprod : Tendsto (fun t => (e.chart hm t).zeta p i*(e.chart hm t).chi p i)
      atTop (𝓝 (-modelA (m := m) p*leadingD s i)) := by
    simpa [modelA,leadingD,normalizedTriangle,ZWSystem.rescale,div_eq_mul_inv,mul_comm] using
      (e.zeta_limit hm p i).mul (e.chi_limit hm p i)
  have hh := actual_root_eventually_sheet hr (cross_base_product_ne s e hm p i) hmetric
    (e.cross_limit hm p i) hprod
  filter_upwards [hh] with t ht
  rw [modelCrossRoot,actual_modelZeta,actual_modelChi]
  exact ht

theorem all_actual_sheets : ∀ᶠ t in atTop,
    (e.chart hm t).point.delta 3 4=modelPairRoot s e (actualCoordinates s e hm t) ∧
    (∀ i j, (e.chart hm t).point.delta (tripleIndex i) (tripleIndex j)=
      modelTriangleRoot s (actualCoordinates s e hm t) i j) ∧
    (∀ p i, (e.chart hm t).cross p i=
      modelCrossRoot s e (e.chart hm t).time (actualCoordinates s e hm t) p i) := by
  exact (actual_pair_sheet s e hm).and
    ((Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => actual_triangle_sheet s e hm i j).and
      (Filter.eventually_all.2 fun p => Filter.eventually_all.2 fun i => actual_cross_sheet s e hm p i))

end
end CentralConfigurations.FiveBody.D2.Regular
