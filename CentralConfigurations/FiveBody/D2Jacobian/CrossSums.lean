import CentralConfigurations.FiveBody.D2Jacobian.ScalarDerivative

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

def hzDerivative (i : Fin 3) : ChartSpace →L[ℂ] ℂ :=
  ∑ p : Fin 2, (m (pairIndex p):ℂ) •
    ((3*modelA (m := m) p*(s.cross p i/e.ratio)^3/(2*leadingD s i)) • dDerivative s i)
def hwDerivative (i : Fin 3) : ChartSpace →L[ℂ] ℂ :=
  ∑ p : Fin 2, (m (pairIndex p):ℂ) •
    ((-(s.cross p i/e.ratio)^3/2) • dDerivative s i)
def gzDerivative (p : Fin 2) : ChartSpace →L[ℂ] ℂ :=
  ∑ i : Fin 3, shapeMass m i •
    ((3*modelA (m := m) p*(s.cross p i/e.ratio)^3/(2*leadingD s i)) • dDerivative s i)
def crossSumZDerivative : ChartSpace →L[ℂ] ℂ :=
  ∑ p : Fin 2, ∑ i : Fin 3, ((m (pairIndex p):ℂ)*shapeMass m i) •
    ((3*modelA (m := m) p*(s.cross p i/e.ratio)^3/(2*leadingD s i)) • dDerivative s i)
def crossSumWDerivative : ChartSpace →L[ℂ] ℂ :=
  ∑ p : Fin 2, ∑ i : Fin 3, ((m (pairIndex p):ℂ)*shapeMass m i) •
    ((-(s.cross p i/e.ratio)^3/2) • dDerivative s i)

include hm in
theorem modelHz_strictFDerivAt (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelHz s e v.1 v.2 i)
      (hzDerivative s e i) (0,baseCoordinates s e) := by
  have hh := HasStrictFDerivAt.fun_sum (u := Finset.univ)
    (fun p _ => (crossForceZ_strictFDerivAt s e hm p i).const_mul (m (pairIndex p):ℂ))
  convert hh using 1
  ext v : 1; apply Finset.sum_congr rfl; intro p _; ring

include hm in
theorem modelHw_strictFDerivAt (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelHw s e v.1 v.2 i)
      (hwDerivative s e i) (0,baseCoordinates s e) := by
  have hh := HasStrictFDerivAt.fun_sum (u := Finset.univ)
    (fun p _ => (crossForceW_strictFDerivAt s e hm p i).const_mul (m (pairIndex p):ℂ))
  convert hh using 1
  ext v : 1; apply Finset.sum_congr rfl; intro p _; ring

include hm in
theorem modelGz_strictFDerivAt (p : Fin 2) :
    HasStrictFDerivAt (fun v : ChartSpace => modelGz s e v.1 v.2 p)
      (gzDerivative s e p) (0,baseCoordinates s e) := by
  have hh := HasStrictFDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => (crossForceZ_strictFDerivAt s e hm p i).const_mul (shapeMass m i))
  convert hh using 1
  ext v : 1; apply Finset.sum_congr rfl; intro i _; ring

include hm in
theorem modelCrossSumZ_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => modelCrossSumZ s e v.1 v.2)
      (crossSumZDerivative s e) (0,baseCoordinates s e) := by
  have hh := HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun p _ =>
    HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (crossForceZ_strictFDerivAt s e hm p i).const_mul ((m (pairIndex p):ℂ)*shapeMass m i)))
  convert hh using 1
  ext v : 1
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro i _; ring

include hm in
theorem modelCrossSumW_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => modelCrossSumW s e v.1 v.2)
      (crossSumWDerivative s e) (0,baseCoordinates s e) := by
  have hh := HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun p _ =>
    HasStrictFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (crossForceW_strictFDerivAt s e hm p i).const_mul ((m (pairIndex p):ℂ)*shapeMass m i)))
  convert hh using 1
  ext v : 1
  apply Finset.sum_congr rfl; intro p _
  apply Finset.sum_congr rfl; intro i _; ring

def jacobianResponse : Fin 3 → ℂ := centeredVector (shapeMass m) (fun i =>
  ((m 3:ℂ)*(s.cross 0 i/e.ratio)+(m 4:ℂ)*(s.cross 1 i/e.ratio))/leadingD s i)

include hm in
theorem modelHz_base (i : Fin 3) :
    modelHz s e 0 (baseCoordinates s e) i=
      ((m 3:ℂ)*(s.cross 0 i/e.ratio)+(m 4:ℂ)*(s.cross 1 i/e.ratio))/leadingD s i := by
  have hf (p : Fin 2) : (s.cross p i/e.ratio)^3*(-modelA (m := m) p)=
      (s.cross p i/e.ratio)/leadingD s i := by
    have hd : leadingD s i≠0 := (mul_ne_zero_iff.mp (cross_base_product_ne s e hm p i)).2
    have hh := cross_base_metric s e hm p i
    field_simp [hd]
    linear_combination (s.cross p i/e.ratio)*hh
  dsimp [modelHz]
  simp_rw [modelCrossRoot_base s e hm,modelZeta_base]
  simp [Fin.sum_univ_succ,pairIndex]
  linear_combination (m 3:ℂ)*hf 0+(m 4:ℂ)*hf 1

include hm in
theorem centeredHz_strictFDerivAt (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => centeredVector (shapeMass m)
      (modelHz s e v.1 v.2) i)
      (hzDerivative s e i-(1/(shapeMass m 0+shapeMass m 1+shapeMass m 2)) •
        ∑ j : Fin 3, shapeMass m j • hzDerivative s e j) (0,baseCoordinates s e) := by
  exact (modelHz_strictFDerivAt s e hm i).sub (scalar_div_strictFDerivAt (HasStrictFDerivAt.fun_sum
    (u := Finset.univ) (fun j _ => (modelHz_strictFDerivAt s e hm j).const_mul (shapeMass m j))) _)

include hm in
theorem centeredHw_strictFDerivAt (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => centeredVector (shapeMass m)
      (modelHw s e v.1 v.2) i)
      (hwDerivative s e i-(1/(shapeMass m 0+shapeMass m 1+shapeMass m 2)) •
        ∑ j : Fin 3, shapeMass m j • hwDerivative s e j) (0,baseCoordinates s e) := by
  exact (modelHw_strictFDerivAt s e hm i).sub (scalar_div_strictFDerivAt (HasStrictFDerivAt.fun_sum
    (u := Finset.univ) (fun j _ => (modelHw_strictFDerivAt s e hm j).const_mul (shapeMass m j))) _)

end
end CentralConfigurations.FiveBody.D2.Regular

