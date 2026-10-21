import CentralConfigurations.Enumeration.ForceComparisonDecisions
import CentralConfigurations.Enumeration.SequenceOrderDomains
import CentralConfigurations.Asymptotics.MaximalTermSupport

/-!
# Leading-support flags for the actual terms of each equation

Diagonal entries represent positions; off-diagonal entries represent forces.
The leading binary matrix certifies their order relative to the common scale.
Nonzero masses and the diagonal minus sign preserve every comparison when
passing to the summands of the zero-sum force equation.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

theorem LeadingOrderFlag.isBigO {b : Bool} {f s : ℕ → ℂ} (h : LeadingOrderFlag b f s) :
    f =O[atTop] s := by
  cases b
  · exact (show f =o[atTop] s from h).isBigO
  · exact h.1

theorem LeadingOrderFlag.theta {b : Bool} {f s : ℕ → ℂ}
    (h : LeadingOrderFlag b f s) (hb : b = true) : f =Θ[atTop] s := by
  simpa only [hb, LeadingOrderFlag, Bool.true_eq, if_true] using h

theorem leadingOrderFlag_of_normalized {f s : ℕ → ℂ} {v : ℂ}
    (hs : ∀ t, s t ≠ 0) (h : Tendsto (fun t => (s t)⁻¹ * f t) atTop (𝓝 v)) :
    LeadingOrderFlag (decide (v ≠ 0)) f s := by
  classical
  by_cases hv : v = 0
  · simpa only [LeadingOrderFlag, hv, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
      if_false] using (normalized_littleO_iff hs h).mpr hv
  · simpa [LeadingOrderFlag, hv] using
      (normalized_theta_iff hs h).mpr hv

namespace ZWSystem

variable {n : ℕ} {mass : Fin n → ℂ}

def zMaxTermValue (q : ZWSystem ℂ n mass) (i j : Fin n) : ℂ :=
  if i = j then q.z i else q.zForce i j

def wMaxTermValue (q : ZWSystem ℂ n mass) (i j : Fin n) : ℂ :=
  if i = j then q.w i else q.wForce i j

theorem zMaxTermValue_theta_equationTerm (q : ℕ → ZWSystem ℂ n mass)
    (hm : ∀ j, mass j ≠ 0) (i j : Fin n) :
    (fun t => (q t).zMaxTermValue i j) =Θ[atTop] (fun t => (q t).zEquationTerm i j) := by
  by_cases hij : i = j
  · subst j
    apply IsTheta.of_norm_eventuallyEq_norm (Eventually.of_forall fun t => ?_)
    simp [zMaxTermValue, zEquationTerm]
  · simpa only [zMaxTermValue, zEquationTerm, if_neg hij, if_neg (Ne.symm hij)] using
      (isTheta_refl (fun t => (q t).zForce i j) atTop).const_mul_right (hm j)

theorem wMaxTermValue_theta_equationTerm (q : ℕ → ZWSystem ℂ n mass)
    (hm : ∀ j, mass j ≠ 0) (i j : Fin n) :
    (fun t => (q t).wMaxTermValue i j) =Θ[atTop] (fun t => (q t).wEquationTerm i j) :=
  zMaxTermValue_theta_equationTerm (fun t => (q t).swap) hm i j

end ZWSystem

namespace ScaledZWLimit

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))

open Classical in
theorem diagramCode_z_entry (i j : Fin n) :
    l.diagramCode.1 (upperIndex i j) = decide (l.z.Incident i j) := by
  classical
  change decide (l.z.matrix _ _ = 1) = _
  rw [symmetric_upperIndex l.z.matrix l.z.matrix_symm i j]
  simp [OneColorLimit.matrix]

open Classical in
theorem diagramCode_w_entry (i j : Fin n) :
    l.diagramCode.2 (upperIndex i j) = decide (l.w.Incident i j) := by
  classical
  change decide (l.w.matrix _ _ = 1) = _
  rw [symmetric_upperIndex l.w.matrix l.w.matrix_symm i j]
  simp [OneColorLimit.matrix]

theorem z_maxTerm_leadingFlag (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀) (i j : Fin n) :
    LeadingOrderFlag (l.diagramCode.1 (upperIndex i j))
      (fun t => (q t).zMaxTermValue i j) (fun t => (‖(q t).zVector‖ : ℂ)) := by
  classical
  have hs (t : ℕ) : (‖(q t).zVector‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i₀ j₀ hij₀))
  rw [l.diagramCode_z_entry]
  by_cases hij : i = j
  · subst j
    simp only [OneColorLimit.Incident, ZWSystem.zMaxTermValue]
    exact leadingOrderFlag_of_normalized hs (l.z_position i)
  · simp only [OneColorLimit.Incident, ZWSystem.zMaxTermValue, if_neg hij]
    exact leadingOrderFlag_of_normalized hs (l.z_force i j)

theorem w_maxTerm_leadingFlag (i₀ j₀ : Fin n) (hij₀ : i₀ ≠ j₀) (i j : Fin n) :
    LeadingOrderFlag (l.diagramCode.2 (upperIndex i j))
      (fun t => (q t).wMaxTermValue i j) (fun t => (‖(q t).zVector‖ : ℂ)) := by
  classical
  have hs (t : ℕ) : (‖(q t).zVector‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr ((q t).zVector_ne_zero i₀ j₀ hij₀))
  rw [l.diagramCode_w_entry]
  by_cases hij : i = j
  · subst j
    simp only [OneColorLimit.Incident, ZWSystem.wMaxTermValue]
    exact leadingOrderFlag_of_normalized hs (l.w_position i)
  · simp only [OneColorLimit.Incident, ZWSystem.wMaxTermValue, if_neg hij]
    exact leadingOrderFlag_of_normalized hs (l.w_force i j)

end ScaledZWLimit
end CentralConfigurations
