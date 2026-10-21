import CentralConfigurations.FiveBody.D2Regular.Gauge
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open Filter
open scoped Topology

/-- The local root through the actual signed value r0. The only principal root
is applied near 1; the original phase is carried by the factor r0. -/
def rootSheet (r0 P0 P : ℂ) : ℂ := r0/Complex.sqrt (P/P0)

theorem rootSheet_self {r0 P0 : ℂ} (hP : P0≠0) : rootSheet r0 P0 P0=r0 := by
  simp [rootSheet,hP]

theorem rootSheet_strictDeriv {r0 P0 : ℂ} (hP : P0≠0) :
    HasStrictDerivAt (rootSheet r0 P0) (-r0/(2*P0)) P0 := by
  have hsq : HasStrictDerivAt Complex.sqrt (1/2:ℂ) (1:ℂ) := by
    simpa using Complex.hasStrictDerivAt_sqrt (z := (1:ℂ)) (by simp [Complex.slitPlane])
  have hs : HasStrictDerivAt (fun P : ℂ => Complex.sqrt (P/P0)) ((1/2)*(1/P0)) P0 := by
    have hsq' : HasStrictDerivAt Complex.sqrt (1/2:ℂ) (id P0/P0) := by simpa [hP] using hsq
    exact HasStrictDerivAt.comp (h₂ := Complex.sqrt) (h := fun P : ℂ => P/P0)
      P0 hsq' ((hasStrictDerivAt_id P0).div_const P0)
  have hh := (hasStrictDerivAt_const P0 r0).div hs (by simp [hP])
  convert hh using 1
  simp [hP]
  ring

theorem rootSheet_metric {r0 P0 P : ℂ} (h0 : r0^2*P0=1) (hP : P≠0) :
    rootSheet r0 P0 P^2*P=1 := by
  have hP0 : P0≠0 := by intro hh; simp [hh] at h0
  have hs : Complex.sqrt (P/P0)^2=P/P0 :=
    Complex.cpow_nat_inv_pow _ (by decide : 2≠0)
  dsimp [rootSheet]
  rw [div_pow,hs]
  field_simp [hP0,hP]
  exact h0

/-- Original metric roots converging to r0 eventually equal that exact local
sheet. This proves sheet retention rather than choosing endpoint signs. -/
theorem actual_root_eventually_sheet {r P : ℕ → ℂ} {r0 P0 : ℂ}
    (hr0 : r0≠0) (hP0 : P0≠0) (hmetric : ∀ t, r t^2*P t=1)
    (hr : Tendsto r atTop (𝓝 r0)) (hP : Tendsto P atTop (𝓝 P0)) :
    ∀ᶠ t in atTop, r t=rootSheet r0 P0 (P t) := by
  have hm0 : r0^2*P0=1 := by
    apply tendsto_nhds_unique ((hr.pow 2).mul hP)
    simpa only [hmetric] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1:ℂ)) atTop (𝓝 1))
  have hs : Tendsto (fun t => rootSheet r0 P0 (P t)) atTop (𝓝 r0) := by
    have hh := (rootSheet_strictDeriv (r0 := r0) hP0).hasDerivAt.continuousAt.tendsto.comp hP
    simpa only [rootSheet_self hP0] using hh
  have hn : r0+r0≠0 := by intro hh; apply hr0; linear_combination hh/2
  filter_upwards [(hr.add hs).eventually_ne hn,hP.eventually_ne hP0] with t ht hPt
  have h1 := hmetric t
  have h2 := rootSheet_metric hm0 hPt
  have he : (r t-rootSheet r0 P0 (P t))*(r t+rootSheet r0 P0 (P t))*P t=0 := by
    linear_combination h1-h2
  exact sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hPt)).resolve_right ht)

end
end CentralConfigurations.FiveBody.D2.Regular
