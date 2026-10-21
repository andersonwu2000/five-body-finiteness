import CentralConfigurations.FiveBody.D2Regular.NormalizedLeading

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter Asymptotics
open scoped Topology BigOperators
set_option maxHeartbeats 2000000

abbrev shapeMass (m : Fin 5 → ℝ) (i : Fin 3) : ℂ := m (tripleIndex i)

theorem parallelCoefficient_limit (n d : Fin 3 → ℂ) {v : ℕ → Fin 3 → ℂ} {v0 : Fin 3 → ℂ}
    (hv : ∀ i, Tendsto (fun t => v t i) atTop (𝓝 (v0 i))) :
    Tendsto (fun t => parallelCoefficient n d (v t)) atTop (𝓝 (parallelCoefficient n d v0)) := by
  exact (tendsto_finsetSum Finset.univ (fun i _ => (hv i).const_mul (n i*d i))).div_const _

theorem transverseCoefficient_limit (n d : Fin 3 → ℂ) {v : ℕ → Fin 3 → ℂ} {v0 : Fin 3 → ℂ}
    (hv : ∀ i, Tendsto (fun t => v t i) atTop (𝓝 (v0 i))) :
    Tendsto (fun t => transverseCoefficient n d (v t)) atTop (𝓝 (transverseCoefficient n d v0)) := by
  exact (((hv 2).sub ((parallelCoefficient_limit n d hv).mul_const (d 2))).const_mul (n 2)).div_const _

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0)

def leadingD : Fin 3 → ℂ := (normalizedTriangle s).w
def leadingE : Fin 3 → ℂ := transverse (shapeMass m) (leadingD s)
def modelC (x : Fin 6 → ℂ) (i : Fin 3) : ℂ :=
  (normalizedKappa s+x 1)*leadingD s i+x 2*leadingE s i
def modelD (x : Fin 6 → ℂ) (i : Fin 3) : ℂ :=
  leadingD s i+x 3*(leadingE s i-leadingE s 2*leadingD s i)

variable (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

def actualCoordinates (t : ℕ) : Fin 6 → ℂ :=
  ![(e.chart hm t).beta,
    parallelCoefficient (shapeMass m) (leadingD s) (e.chart hm t).c-normalizedKappa s,
    transverseCoefficient (shapeMass m) (leadingD s) (e.chart hm t).c,
    transverseCoefficient (shapeMass m) (leadingD s) (e.chart hm t).d,
    (e.chart hm t).etaZ,(e.chart hm t).etaW]

def baseCoordinates : Fin 6 → ℂ := ![e.betaValue,0,0,0,e.etaZValue,e.etaWValue]

theorem actual_modelC (t : ℕ) (i : Fin 3) :
    modelC s (actualCoordinates s e hm t) i=(e.chart hm t).c i := by
  have hh := plane_decomposition (shapeMass m) (leadingD s) (e.chart hm t).c
    (fun j => Complex.ofReal_ne_zero.mpr (ne_of_gt (hm (tripleIndex j))))
    ((normalizedTriangle s).w_separation_ne_zero (by decide)) (normalized_nonisotropic s)
    (normalizedTriangle s).mass_center_w (e.chart hm t).c_centered i
  dsimp [modelC,actualCoordinates,leadingE]
  linear_combination -hh

theorem actual_modelD (t : ℕ) (i : Fin 3) :
    modelD s (actualCoordinates s e hm t) i=(e.chart hm t).d i := by
  exact (gauge_plane_decomposition (shapeMass m) (leadingD s) (e.chart hm t).d
    (fun j => Complex.ofReal_ne_zero.mpr (ne_of_gt (hm (tripleIndex j))))
    ((normalizedTriangle s).w_separation_ne_zero (by decide)) (normalized_nonisotropic s)
    (normalizedTriangle s).mass_center_w (e.chart hm t).d_centered
    (normalized_last s) (e.chart hm t).d_last i).symm

theorem base_modelC (i : Fin 3) : modelC s (baseCoordinates s e) i=(normalizedTriangle s).z i := by
  dsimp [modelC,baseCoordinates,leadingD]
  rw [add_zero,zero_mul,add_zero]
  exact (normalized_proportional s i).symm

theorem base_modelD (i : Fin 3) : modelD s (baseCoordinates s e) i=(normalizedTriangle s).w i := by
  simp [modelD,baseCoordinates,leadingD]

theorem actual_coordinates_limit : Tendsto (actualCoordinates s e hm) atTop (𝓝 (baseCoordinates s e)) := by
  have hc : ∀ i, Tendsto (fun t => (e.chart hm t).c i) atTop (𝓝 ((normalizedTriangle s).z i)) :=
    fun i => e.c_limit hm i
  have hd : ∀ i, Tendsto (fun t => (e.chart hm t).d i) atTop (𝓝 (leadingD s i)) := by
    intro i
    simpa [leadingD,normalizedTriangle,ZWSystem.rescale,div_eq_mul_inv,mul_comm] using e.d_limit hm i
  have he : (normalizedTriangle s).z=fun i => normalizedKappa s*leadingD s i :=
    funext (normalized_proportional s)
  have hp := parallelCoefficient_limit (shapeMass m) (leadingD s) hc
  have hv := transverseCoefficient_limit (shapeMass m) (leadingD s) hc
  rw [he,parallel_smul,parallel_self (shapeMass m) (leadingD s) (normalized_nonisotropic s),mul_one] at hp
  rw [he,transverse_smul,transverse_self (shapeMass m) (leadingD s) (normalized_nonisotropic s),mul_zero] at hv
  have hy := transverseCoefficient_limit (shapeMass m) (leadingD s) hd
  rw [transverse_self (shapeMass m) (leadingD s) (normalized_nonisotropic s)] at hy
  apply tendsto_pi_nhds.2
  intro i
  fin_cases i
  · exact e.beta_limit hm
  · simpa only [sub_self] using hp.sub_const (normalizedKappa s)
  · exact hv
  · exact hy
  · exact e.etaZ_limit hm
  · exact e.etaW_limit hm

end
end CentralConfigurations.FiveBody.D2.Regular
