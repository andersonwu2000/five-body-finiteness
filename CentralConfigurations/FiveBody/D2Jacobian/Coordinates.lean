import CentralConfigurations.FiveBody.D2Regular.BaseResidual
import CentralConfigurations.FiveBody.D2Regular.ForceDerivative
import CentralConfigurations.FiveBody.D2Regular.ResponseAlgebra
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Normed.Module.FiniteDimension

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators

abbrev ChartSpace := ℂ × (Fin 6 → ℂ)

def hCoord : ChartSpace →L[ℂ] ℂ := ContinuousLinearMap.fst ℂ ℂ (Fin 6 → ℂ)
def chartCoord (i : Fin 6) : ChartSpace →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ ℂ (Fin 6 → ℂ))

@[simp] theorem hCoord_apply (v : ChartSpace) : hCoord v=v.1 := rfl
@[simp] theorem chartCoord_apply (i : Fin 6) (v : ChartSpace) : chartCoord i v=v.2 i := rfl

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit)

def cDerivative (i : Fin 3) : ChartSpace →L[ℂ] ℂ :=
  leadingD s i • chartCoord 1+leadingE s i • chartCoord 2
def dDerivative (i : Fin 3) : ChartSpace →L[ℂ] ℂ :=
  (leadingE s i-leadingE s 2*leadingD s i) • chartCoord 3

theorem modelC_strictFDerivAt (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelC s v.2 i)
      (cDerivative s i) (0,baseCoordinates s e) := by
  convert (((chartCoord 1).hasStrictFDerivAt.add_const (normalizedKappa s)).mul_const
    (leadingD s i)).add ((chartCoord 2).hasStrictFDerivAt.mul_const (leadingE s i)) using 1
  funext v
  simp only [modelC,chartCoord_apply,Pi.add_apply]
  ring

theorem modelD_strictFDerivAt (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelD s v.2 i)
      (dDerivative s i) (0,baseCoordinates s e) := by
  convert ((chartCoord 3).hasStrictFDerivAt.mul_const
    (leadingE s i-leadingE s 2*leadingD s i)).const_add (leadingD s i) using 1

theorem h_squared_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => v.1^2) (0 : ChartSpace →L[ℂ] ℂ)
      (0,baseCoordinates s e) := by
  exact (hCoord.hasStrictFDerivAt.pow 2 (x := (0,baseCoordinates s e))).congr_fderiv (by
    apply ContinuousLinearMap.ext; intro v
    simp [ContinuousLinearMap.smul_apply,smul_eq_mul])

theorem h_cubed_strictFDerivAt :
    HasStrictFDerivAt (fun v : ChartSpace => v.1^3) (0 : ChartSpace →L[ℂ] ℂ)
      (0,baseCoordinates s e) := by
  exact (hCoord.hasStrictFDerivAt.pow 3 (x := (0,baseCoordinates s e))).congr_fderiv (by
    apply ContinuousLinearMap.ext; intro v
    simp [ContinuousLinearMap.smul_apply,smul_eq_mul])

theorem modelZeta_strictFDerivAt (p : Fin 2) (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelZeta s v.1 v.2 p i)
      (0 : ChartSpace →L[ℂ] ℂ) (0,baseCoordinates s e) := by
  exact ((((h_squared_strictFDerivAt s e).mul
    (modelC_strictFDerivAt s e i)).const_add (-modelA (m := m) p)).add
    ((h_cubed_strictFDerivAt s e).mul (chartCoord 4).hasStrictFDerivAt)).congr_fderiv (by
    apply ContinuousLinearMap.ext; intro v; simp [ContinuousLinearMap.smul_apply,smul_eq_mul])

theorem modelChi_strictFDerivAt (p : Fin 2) (i : Fin 3) :
    HasStrictFDerivAt (fun v : ChartSpace => modelChi s v.1 v.2 p i)
      (dDerivative s i) (0,baseCoordinates s e) := by
  exact (((modelD_strictFDerivAt s e i).sub
    ((h_squared_strictFDerivAt s e).mul
      ((chartCoord 0).hasStrictFDerivAt.mul_const (modelA (m := m) p)))).add
    ((h_cubed_strictFDerivAt s e).mul (chartCoord 5).hasStrictFDerivAt)).congr_fderiv (by
    apply ContinuousLinearMap.ext; intro v; simp [ContinuousLinearMap.smul_apply,smul_eq_mul])

end
end CentralConfigurations.FiveBody.D2.Regular


