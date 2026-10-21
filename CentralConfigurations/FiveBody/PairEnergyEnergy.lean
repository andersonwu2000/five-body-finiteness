import CentralConfigurations.FiveBody.PairEnergyLimits
import CentralConfigurations.FiveBody.PairEnergyMassGap

namespace CentralConfigurations.FiveBody.PairEnergy
open Filter Asymptotics
open scoped Topology BigOperators

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass} {b : Bool}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (hd : l.diagramCode=akDiagram b)
include l hd

/-- The complete exact inertia identity, including both residual terms,
forces the binary invariant cube on all signed pair sheets. -/
theorem invariant_cube {I : ℂ} (hI : ∀ t, (q t).toNormalized.potential=I)
    (hP : pairMass mass ≠ 0) (hK : tripleMass mass ≠ 0) :
    pairMass mass*I^3=(mass 0*mass 1)^3 := by
  have hres := ((triple_metric_residual_zero l hd).const_mul (pairMass mass)).add
    ((pair_center_product_zero l hd).const_mul (pairMass mass+tripleMass mass))
  have h := (tendsto_const_nhds : Tendsto
    (fun _ : ℕ => pairMass mass*tripleMass mass*I) atTop
    (𝓝 (pairMass mass*tripleMass mass*I))).sub hres
  have heq t : pairMass mass*tripleMass mass*I -
      (pairMass mass*tripleMetric (q t)+(pairMass mass+tripleMass mass)*(pairZ (q t)*pairW (q t))) =
      mass 0*mass 1*tripleMass mass*D q 0 1 t := by
    have hi := full_inertia (q t)
    rw [hI t] at hi
    dsimp [D]
    linear_combination hi
  have hp : Tendsto (fun t => mass 0*mass 1*tripleMass mass*D q 0 1 t) atTop
      (𝓝 (pairMass mass*tripleMass mass*I)) := by
    simpa only [mul_zero,add_zero,sub_zero] using h.congr heq
  have hcube := hp.pow 3
  have hmetric := (pair_metric_cube_limit l hd hP).const_mul ((mass 0*mass 1*tripleMass mass)^3)
  have hh : (pairMass mass*tripleMass mass*I)^3 =
      (mass 0*mass 1*tripleMass mass)^3*(pairMass mass)^2 := by
    exact tendsto_nhds_unique (hcube.congr (fun t => by ring)) hmetric
  have hzero : (pairMass mass^2*tripleMass mass^3)*
      (pairMass mass*I^3-(mass 0*mass 1)^3)=0 := by linear_combination hh
  exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left
    (mul_ne_zero (pow_ne_zero 2 hP) (pow_ne_zero 3 hK)))

omit l hd

theorem false_of_ak_diagram {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))} {b : Bool}
    (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hm : ∀ i, 0<m i) (hd : l.diagramCode=akDiagram b)
    {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
    (hI : ∀ t, (q t).toNormalized.potential=(I0:ℂ)) : False := by
  have hm0 := hm 0; have hm1 := hm 1; have hm2 := hm 2
  have hm3 := hm 3; have hm4 := hm 4
  have hP : pairMass (fun i => (m i : ℂ)) ≠ 0 := by
    dsimp [pairMass]
    exact_mod_cast ne_of_gt (add_pos hm0 hm1)
  have hK : tripleMass (fun i => (m i : ℂ)) ≠ 0 := by
    dsimp [tripleMass]
    exact_mod_cast ne_of_gt (show 0<m 2+m 3+m 4 by positivity)
  have hcube := invariant_cube l hd hI hP hK
  have hreal : (m 0+m 1)*I0^3=(m 0*m 1)^3 := by
    dsimp [pairMass] at hcube
    exact_mod_cast hcube
  exact physical_scalar_not_binary hm hphysical hreal

end CentralConfigurations.FiveBody.PairEnergy
