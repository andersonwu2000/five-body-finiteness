import CentralConfigurations.FiveBody.D2Regular.FiniteResidual

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

include hm in
theorem pair_base_product_ne : pairMass (fun i => (m i:ℂ))^2*e.betaValue≠0 := by
  intro hh
  have he := e.pair_leading_metric hm
  rw [mul_assoc,hh,mul_zero] at he
  exact zero_ne_one he

theorem triangle_base_product_ne (i j : Fin 3) (hij : i≠j) :
    ((normalizedTriangle s).z i-(normalizedTriangle s).z j)*(leadingD s i-leadingD s j)≠0 :=
  mul_ne_zero ((normalizedTriangle s).z_separation_ne_zero hij)
    ((normalizedTriangle s).w_separation_ne_zero hij)

include hm in
theorem cross_base_metric (p : Fin 2) (i : Fin 3) :
    (s.cross p i/e.ratio)^2*(-modelA (m := m) p*leadingD s i)=1 := by
  have hh := e.cross_leading_metric hm p i
  simpa only [leadingD,normalizedTriangle,ZWSystem.rescale,modelA,div_eq_mul_inv,mul_assoc,
    mul_left_comm,mul_comm] using hh

include e hm in
theorem cross_base_product_ne (p : Fin 2) (i : Fin 3) : -modelA (m := m) p*leadingD s i≠0 := by
  intro hh
  have he := cross_base_metric s e hm p i
  rw [hh,mul_zero] at he
  exact zero_ne_one he

include hm in
theorem modelPairRoot_base : modelPairRoot s e (baseCoordinates s e)=s.pairDelta := by
  exact rootSheet_self (pair_base_product_ne s e hm)

theorem modelTriangleRoot_base (i j : Fin 3) :
    modelTriangleRoot s (baseCoordinates s e) i j=s.triangle.delta i j := by
  by_cases hij : i=j
  · subst j
    simp [modelTriangleRoot,s.triangle.delta_diagonal]
  · dsimp [modelTriangleRoot]
    rw [if_neg hij,base_modelC,base_modelC,base_modelD,base_modelD]
    exact rootSheet_self (triangle_base_product_ne s i j hij)

theorem modelZeta_base (p : Fin 2) (i : Fin 3) :
    modelZeta s 0 (baseCoordinates s e) p i= -modelA (m := m) p := by simp [modelZeta]

theorem modelChi_base (p : Fin 2) (i : Fin 3) :
    modelChi s 0 (baseCoordinates s e) p i=leadingD s i := by
  simp [modelChi,base_modelD,leadingD]

include hm in
theorem modelCrossRoot_base (p : Fin 2) (i : Fin 3) :
    modelCrossRoot s e 0 (baseCoordinates s e) p i=s.cross p i/e.ratio := by
  dsimp [modelCrossRoot]
  rw [modelZeta_base,modelChi_base]
  exact rootSheet_self (cross_base_product_ne s e hm p i)

theorem modelFz_base (i : Fin 3) : modelFz s (baseCoordinates s e) i=0 := by
  dsimp [modelFz]
  simp_rw [base_modelC,modelTriangleRoot_base]
  exact sub_eq_zero.mpr ((normalizedTriangle s).force_z i)

theorem modelFw_base (i : Fin 3) : modelFw s (baseCoordinates s e) i=0 := by
  dsimp [modelFw]
  simp_rw [base_modelD,modelTriangleRoot_base]
  exact sub_eq_zero.mpr ((normalizedTriangle s).force_w i)

include hm in
theorem zetaValue_eq (p : Fin 2) : e.zetaValue p= -modelA (m := m) p :=
  tendsto_nhds_unique (e.zeta_limit_raw hm p 0) (e.zeta_limit hm p 0)

include hm in
theorem modelCrossSumZ_base :
    (pairMass (fun i => (m i:ℂ))+tripleMass (fun i => (m i:ℂ)))/
      (pairMass (fun i => (m i:ℂ))*tripleMass (fun i => (m i:ℂ)))*
      modelCrossSumZ s e 0 (baseCoordinates s e)=e.etaZValue := by
  dsimp [modelCrossSumZ,GaugeExtraction.etaZValue]
  simp_rw [modelCrossRoot_base s e hm,modelZeta_base,zetaValue_eq s e hm]

include hm in
theorem modelCrossSumW_base :
    (pairMass (fun i => (m i:ℂ))+tripleMass (fun i => (m i:ℂ)))/
      (pairMass (fun i => (m i:ℂ))*tripleMass (fun i => (m i:ℂ)))*
      modelCrossSumW s e 0 (baseCoordinates s e)=e.etaWValue := by
  dsimp [modelCrossSumW,GaugeExtraction.etaWValue]
  simp_rw [modelCrossRoot_base s e hm,modelChi_base]
  simp [leadingD,normalizedTriangle,ZWSystem.rescale,div_eq_mul_inv,mul_comm]

include hm in
theorem finiteResidual_base : finiteResidual s e 0 (baseCoordinates s e)=0 := by
  have hp : pairMass (fun i => (m i:ℂ))*s.pairDelta^3=1 := by
    rw [s.pair_delta_cube]
    apply mul_inv_cancel₀
    change (m 3:ℂ)+m 4≠0
    exact_mod_cast ne_of_gt (add_pos (hm 3) (hm 4))
  funext i
  fin_cases i
  · simp [finiteResidual,modelPairRoot_base s e hm,hp]
  · simp [finiteResidual,modelTripleResidualW,modelFw_base,bilinear]
  · simp [finiteResidual,modelTripleResidualZ,modelFz_base,bilinear]
  · simp [finiteResidual,modelTripleResidualW,modelFw_base,bilinear]
  · change e.etaZValue-_=0
    rw [modelCrossSumZ_base s e hm,sub_self]
  · change e.etaWValue-_=0
    rw [modelCrossSumW_base s e hm,sub_self]

end
end CentralConfigurations.FiveBody.D2.Regular
