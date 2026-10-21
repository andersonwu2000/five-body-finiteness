import CentralConfigurations.FiveBody.D2Regular.ActualCoordinates
import CentralConfigurations.FiveBody.D2Regular.RootSheet
import CentralConfigurations.FiveBody.D2Regular.LeadingResponse

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit)

def modelA (p : Fin 2) : ℂ := ![-(m 4:ℂ),(m 3:ℂ)] p

def modelPairRoot (x : Fin 6 → ℂ) : ℂ :=
  rootSheet s.pairDelta (pairMass (fun i => (m i:ℂ))^2*e.betaValue)
    (pairMass (fun i => (m i:ℂ))^2*x 0)

def modelTriangleRoot (x : Fin 6 → ℂ) (i j : Fin 3) : ℂ :=
  if i=j then 0 else rootSheet (s.triangle.delta i j)
    (((normalizedTriangle s).z i-(normalizedTriangle s).z j)*(leadingD s i-leadingD s j))
    ((modelC s x i-modelC s x j)*(modelD s x i-modelD s x j))

def modelZeta (h : ℂ) (x : Fin 6 → ℂ) (p : Fin 2) (i : Fin 3) : ℂ :=
  -modelA (m := m) p+h^2*modelC s x i+h^3*x 4
def modelChi (h : ℂ) (x : Fin 6 → ℂ) (p : Fin 2) (i : Fin 3) : ℂ :=
  modelD s x i-h^2*(x 0*modelA (m := m) p)+h^3*x 5
def modelCrossRoot (h : ℂ) (x : Fin 6 → ℂ) (p : Fin 2) (i : Fin 3) : ℂ :=
  rootSheet (s.cross p i/e.ratio) (-modelA (m := m) p*leadingD s i)
    (modelZeta s h x p i*modelChi s h x p i)

def modelHz (h : ℂ) (x : Fin 6 → ℂ) (i : Fin 3) : ℂ :=
  ∑ p : Fin 2, (m (pairIndex p):ℂ)*modelCrossRoot s e h x p i^3*modelZeta s h x p i
def modelHw (h : ℂ) (x : Fin 6 → ℂ) (i : Fin 3) : ℂ :=
  ∑ p : Fin 2, (m (pairIndex p):ℂ)*modelCrossRoot s e h x p i^3*modelChi s h x p i
def modelGz (h : ℂ) (x : Fin 6 → ℂ) (p : Fin 2) : ℂ :=
  ∑ i : Fin 3, shapeMass m i*modelCrossRoot s e h x p i^3*modelZeta s h x p i

def modelFz (x : Fin 6 → ℂ) (i : Fin 3) : ℂ :=
  modelC s x i-∑ j : Fin 3, shapeMass m j*modelTriangleRoot s x i j^3*
    (modelC s x i-modelC s x j)
def modelFw (x : Fin 6 → ℂ) (i : Fin 3) : ℂ :=
  modelD s x i-∑ j : Fin 3, shapeMass m j*modelTriangleRoot s x i j^3*
    (modelD s x i-modelD s x j)

def modelTripleResidualZ (h : ℂ) (x : Fin 6 → ℂ) (i : Fin 3) : ℂ :=
  modelFz s x i-h*centeredVector (shapeMass m) (modelHz s e h x) i
def modelTripleResidualW (h : ℂ) (x : Fin 6 → ℂ) (i : Fin 3) : ℂ :=
  modelFw s x i-h^3*centeredVector (shapeMass m) (modelHw s e h x) i

def modelCrossSumZ (h : ℂ) (x : Fin 6 → ℂ) : ℂ :=
  ∑ p : Fin 2, ∑ i : Fin 3, (m (pairIndex p):ℂ)*shapeMass m i*
    modelCrossRoot s e h x p i^3*modelZeta s h x p i
def modelCrossSumW (h : ℂ) (x : Fin 6 → ℂ) : ℂ :=
  ∑ p : Fin 2, ∑ i : Fin 3, (m (pairIndex p):ℂ)*shapeMass m i*
    modelCrossRoot s e h x p i^3*modelChi s h x p i

/-- Six explicit selected residual equations. The complete original force
system is retained separately in ActualChart; no row-rank premise is assumed. -/
def finiteResidual (h : ℂ) (x : Fin 6 → ℂ) : Fin 6 → ℂ :=
  let A := pairMass (fun i => (m i:ℂ))
  let B := tripleMass (fun i => (m i:ℂ))
  ![(1-A*modelPairRoot s e x^3)+h^3*(modelGz s e h x 0-
      (∑ p : Fin 2, (m (pairIndex p):ℂ)*modelGz s e h x p)/A)/modelA (m := m) 0,
    bilinear (shapeMass m) (leadingD s) (modelTripleResidualW s e h x),
    bilinear (shapeMass m) (leadingE s) (modelTripleResidualZ s e h x),
    bilinear (shapeMass m) (leadingE s) (modelTripleResidualW s e h x),
    x 4-(A+B)/(A*B)*modelCrossSumZ s e h x,
    x 5-(A+B)/(A*B)*modelCrossSumW s e h x]

def augmentedResidual (v : ℂ × (Fin 6 → ℂ)) : ℂ × (Fin 6 → ℂ) :=
  (v.1,finiteResidual s e v.1 v.2)

def modelUnsquaredTorque (h : ℂ) (x : Fin 6 → ℂ) : ℂ :=
  ∑ p : Fin 2, ∑ i : Fin 3, (m (pairIndex p):ℂ)*shapeMass m i*modelCrossRoot s e h x p i

end
end CentralConfigurations.FiveBody.D2.Regular
