import CentralConfigurations.Asymptotics.Balancing
import Mathlib.Analysis.Asymptotics.Theta

/-!
# The meaning of circles, strokes, and closeness

The thesis writes f ≈ R for two-sided order comparability, formalized here by
mathlib's IsTheta. A convergent normalized coefficient is nonzero exactly when
the original sequence has order R. Equality of leading positions is exactly
little-o closeness of their separation. Thus nonzero support is connected to
the thesis's definitions, rather than merely being a substitute graph model.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

theorem normalized_theta_iff {f r : ℕ → ℂ} {v : ℂ}
    (hr : ∀ t, r t ≠ 0)
    (h : Tendsto (fun t => (r t)⁻¹ * f t) atTop (𝓝 v)) :
    (f =Θ[atTop] r) ↔ v ≠ 0 := by
  have hdiv : Tendsto (fun t => f t / r t) atTop (𝓝 v) := by
    simpa only [div_eq_inv_mul] using h
  constructor
  · intro ht hv
    rw [hv] at hdiv
    have ho : f =o[atTop] r :=
      (isLittleO_iff_tendsto (fun t ht => (hr t ht).elim)).mpr hdiv
    exact isLittleO_irrefl (Eventually.of_forall hr).frequently (ht.2.trans_isLittleO ho)
  · intro hv
    exact (isTheta_of_div_tendsto_nhds_ne_zero hdiv hv).symm

theorem normalized_littleO_iff {f r : ℕ → ℂ} {v : ℂ}
    (hr : ∀ t, r t ≠ 0)
    (h : Tendsto (fun t => (r t)⁻¹ * f t) atTop (𝓝 v)) :
    (f =o[atTop] r) ↔ v = 0 := by
  have hdiv : Tendsto (fun t => f t / r t) atTop (𝓝 v) := by
    simpa only [div_eq_inv_mul] using h
  constructor
  · intro ho
    exact tendsto_nhds_unique hdiv ho.tendsto_div_nhds_zero
  · intro hv
    exact (isLittleO_iff_tendsto (fun t ht => (hr t ht).elim)).mpr (hv ▸ hdiv)

theorem normalized_separation_littleO_iff {f g r : ℕ → ℂ} {u v : ℂ}
    (hr : ∀ t, r t ≠ 0)
    (hf : Tendsto (fun t => (r t)⁻¹ * f t) atTop (𝓝 u))
    (hg : Tendsto (fun t => (r t)⁻¹ * g t) atTop (𝓝 v)) :
    ((fun t => f t - g t) =o[atTop] r) ↔ u = v := by
  have hdiff : Tendsto (fun t => (r t)⁻¹ * (f t - g t)) atTop (𝓝 (u - v)) := by
    simpa only [mul_sub] using hf.sub hg
  exact (normalized_littleO_iff hr hdiff).trans sub_eq_zero

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
variable (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀)
include i₀ j₀ hij₀

theorem z_circle_order_iff (i : Fin n) :
    ((fun t => (q t).z i) =Θ[atTop] (fun t => (‖(q t).zVector‖ : ℂ))) ↔ l.z.position i ≠ 0 := by
  exact normalized_theta_iff (fun t => Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i₀ j₀ hij₀))) (l.z_position i)

theorem w_circle_order_iff (i : Fin n) :
    ((fun t => (q t).w i) =Θ[atTop] (fun t => (‖(q t).zVector‖ : ℂ))) ↔ l.w.position i ≠ 0 := by
  exact normalized_theta_iff (fun t => Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i₀ j₀ hij₀))) (l.w_position i)

theorem z_stroke_order_iff (i j : Fin n) :
    ((fun t => (q t).zForce i j) =Θ[atTop] (fun t => (‖(q t).zVector‖ : ℂ))) ↔ l.z.force i j ≠ 0 := by
  exact normalized_theta_iff (fun t => Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i₀ j₀ hij₀))) (l.z_force i j)

theorem w_stroke_order_iff (i j : Fin n) :
    ((fun t => (q t).wForce i j) =Θ[atTop] (fun t => (‖(q t).zVector‖ : ℂ))) ↔ l.w.force i j ≠ 0 := by
  exact normalized_theta_iff (fun t => Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i₀ j₀ hij₀))) (l.w_force i j)

theorem z_close_iff (i j : Fin n) :
    ((fun t => (q t).z i - (q t).z j) =o[atTop] (fun t => (‖(q t).zVector‖ : ℂ))) ↔
      l.z.position i = l.z.position j := by
  exact normalized_separation_littleO_iff (fun t => Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i₀ j₀ hij₀))) (l.z_position i) (l.z_position j)

theorem w_close_iff (i j : Fin n) :
    ((fun t => (q t).w i - (q t).w j) =o[atTop] (fun t => (‖(q t).zVector‖ : ℂ))) ↔
      l.w.position i = l.w.position j := by
  exact normalized_separation_littleO_iff (fun t => Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i₀ j₀ hij₀))) (l.w_position i) (l.w_position j)

theorem z_separation_order_iff (i j : Fin n) :
    ((fun t => (q t).z i - (q t).z j) =Θ[atTop] (fun t => (‖(q t).zVector‖ : ℂ))) ↔
      l.z.position i ≠ l.z.position j := by
  have h : Tendsto (fun t => (q t).inverseScale * ((q t).z i - (q t).z j)) atTop
      (𝓝 (l.z.position i - l.z.position j)) := by
    simpa only [mul_sub] using (l.z_position i).sub (l.z_position j)
  exact (normalized_theta_iff (fun t => Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i₀ j₀ hij₀))) h).trans sub_ne_zero

theorem w_separation_order_iff (i j : Fin n) :
    ((fun t => (q t).w i - (q t).w j) =Θ[atTop] (fun t => (‖(q t).zVector‖ : ℂ))) ↔
      l.w.position i ≠ l.w.position j := by
  have h : Tendsto (fun t => (q t).inverseScale * ((q t).w i - (q t).w j)) atTop
      (𝓝 (l.w.position i - l.w.position j)) := by
    simpa only [mul_sub] using (l.w_position i).sub (l.w_position j)
  exact (normalized_theta_iff (fun t => Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i₀ j₀ hij₀))) h).trans sub_ne_zero

end ScaledZWLimit
end CentralConfigurations
