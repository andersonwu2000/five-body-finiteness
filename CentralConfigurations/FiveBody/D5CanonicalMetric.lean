import CentralConfigurations.FiveBody.D5MetricBound
import CentralConfigurations.FiveBody.D9Exclusion
import CentralConfigurations.Asymptotics.FourProductDominance

namespace CentralConfigurations.FiveBody.D5
open Filter Asymptotics
open scoped Topology BigOperators

theorem eps_relabel {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass)
    (e : Equiv.Perm (Fin 5)) (t : ℕ) :
    eps (fun t => (q t).relabel e) t = eps q t := by
  simp only [eps,ZWSystem.epsilon,ZWSystem.zVector_norm_relabel]

theorem potential_relabel {mass : Fin 5 → ℂ} (q : ZWSystem ℂ 5 mass)
    (e : Equiv.Perm (Fin 5)) :
    (q.relabel e).toNormalized.potential=q.toNormalized.potential := by
  rw [zw_potential,zw_potential]
  exact Equiv.sum_comp e (fun i => mass i*q.z i*q.w i)

theorem canonical_internal (i : Fin 5) : canonicalToAKRoles.symm i < 3 ↔ 2 ≤ i := by
  fin_cases i <;> decide +kernel

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (hd : l.diagramCode=fiveBodySourceDiagram 2)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
  {I0 : ℝ} (hphysical : PhysicalPotentialLevel m I0)
  (hI : ∀ t, (q t).toNormalized.potential=(I0:ℂ))

include l hm hb hd ha hphysical hI

/-- AK D5 is Chang's printed third diagram. This theorem is stated on the
original actual sequence, with no choice of attachment rates. -/
theorem metric_small_of_chang3 (i j : Fin 5) :
    D q i j =o[atTop] (fun t => (eps q t)⁻¹) := by
  let qr := fun t => (q t).relabel canonicalToAKRoles
  let lr := l.relabelCanonical canonicalToAKRoles
  have hdr : lr.diagramCode=akD5Diagram := by
    rw [show lr.diagramCode=DiagramCode.relabel l.diagramCode canonicalToAKRoles from
      l.diagramCode_relabelCanonical canonicalToAKRoles,hd]
    exact chang3_to_akD5
  have hbr : ∀ t, ‖(qr t).zVector‖=‖(qr t).wVector‖ := by
    simpa only [qr,ZWSystem.zVector_norm_relabel,ZWSystem.wVector_norm_relabel] using hb
  have har : Tendsto (fun t => (qr t).inverseScale) atTop (𝓝 0) := by
    simpa only [qr,ZWSystem.inverseScale_relabel] using ha
  have hIr : ∀ t, (qr t).toNormalized.potential=(I0:ℂ) := by
    intro t; rw [potential_relabel]; exact hI t
  have hh := metric_small_of_akD5 lr (fun i => hm (canonicalToAKRoles i)) hbr hdr har
    (D9.physical_level_relabel hphysical canonicalToAKRoles) hIr
    (canonicalToAKRoles.symm i) (canonicalToAKRoles.symm j)
  change (fun t => D qr (canonicalToAKRoles.symm i) (canonicalToAKRoles.symm j) t)
    =o[atTop] (fun t => (eps qr t)⁻¹) at hh
  simp only [qr,eps_relabel] at hh
  simpa only [D,Z,W,ZWSystem.relabel,Equiv.apply_symm_apply] using hh

omit hm ha hphysical hI
theorem internal_metric_bigO_of_chang3 (i j : Fin 5) (hi : 2 ≤ i) (hj : 2 ≤ j) :
    D q i j =O[atTop] (fun t => eps q t^2) := by
  let qr := fun t => (q t).relabel canonicalToAKRoles
  let lr := l.relabelCanonical canonicalToAKRoles
  have hdr : lr.diagramCode=akD5Diagram := by
    rw [show lr.diagramCode=DiagramCode.relabel l.diagramCode canonicalToAKRoles from
      l.diagramCode_relabelCanonical canonicalToAKRoles,hd]
    exact chang3_to_akD5
  have hbr : ∀ t, ‖(qr t).zVector‖=‖(qr t).wVector‖ := by
    simpa only [qr,ZWSystem.zVector_norm_relabel,ZWSystem.wVector_norm_relabel] using hb
  have hh := triangle_orders lr hbr hdr (canonicalToAKRoles.symm i) (canonicalToAKRoles.symm j)
    ((canonical_internal i).2 hi) ((canonical_internal j).2 hj)
  have hmul := hh.1.mul hh.2
  change (fun t => D qr (canonicalToAKRoles.symm i) (canonicalToAKRoles.symm j) t)
    =O[atTop] (fun t => eps qr t * eps qr t) at hmul
  simp only [qr,eps_relabel] at hmul
  simpa only [D,Z,W,ZWSystem.relabel,Equiv.apply_symm_apply,pow_two] using hmul

omit l hb hd

abbrev edgeMetric {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass) (e : Fin 10) :=
  D q (fiveBodyEdges e).1 (fiveBodyEdges e).2

theorem original_fourProduct {mass : Fin 5 → ℂ} (q : ℕ → ZWSystem ℂ 5 mass)
    (t : ℕ) (e : Fin 10) :
    (q t).toNormalized.fiveBodyFourProduct e =
      fiveBodyFourProducts (fun k => edgeMetric q k t) e := by
  unfold NormalizedSystem.fiveBodyFourProduct
  congr 1
  funext k
  exact inverse_zw_separation _ _ _ _

end CentralConfigurations.FiveBody.D5
