import CentralConfigurations.Enumeration.OrderComparisonPrimitives
import CentralConfigurations.Asymptotics.ForceOrderComparison

/-!
# Decision trees for the source's force comparisons

The finite outputs retain the Appendix II priority: leading support first,
then strict algebraic comparisons, equality cases, and reverse comparisons.
All branches are proved for the actual inverse-distance branch.
-/

namespace CentralConfigurations

open Filter Asymptotics

def OrderComparison.orElse (c d : OrderComparison) : OrderComparison :=
  if c = .unknown then d else c

theorem OrderComparison.Valid.orElse {c d : OrderComparison} {f g : ℕ → ℂ}
    (hc : c.Valid f g) (hd : d.Valid f g) : (c.orElse d).Valid f g := by
  unfold OrderComparison.orElse
  split_ifs
  · exact hd
  · exact hc

theorem OrderComparison.Valid.congr_theta {c : OrderComparison} {f g f' g' : ℕ → ℂ}
    (h : c.Valid f g) (hf : f =Θ[atTop] f') (hg : g =Θ[atTop] g') : c.Valid f' g' := by
  cases c with
  | unknown => trivial
  | less => exact (hf.symm.trans_isLittleO h).trans_isTheta hg
  | equal => exact hf.symm.trans (h.trans hg)
  | greater => exact (hg.symm.trans_isLittleO h).trans_isTheta hf

def LeadingOrderFlag (b : Bool) (f s : ℕ → ℂ) : Prop :=
  if b then f =Θ[atTop] s else f =o[atTop] s

def compareLeadingFlags : Bool → Bool → OrderComparison
  | true, true => .equal
  | true, false => .greater
  | false, true => .less
  | false, false => .unknown

theorem compareLeadingFlags_valid {a b : Bool} {f g s : ℕ → ℂ}
    (hf : LeadingOrderFlag a f s) (hg : LeadingOrderFlag b g s) :
    (compareLeadingFlags a b).Valid f g := by
  cases a <;> cases b
  · trivial
  · exact hf.trans_isTheta hg.symm
  · exact hg.trans_isTheta hf.symm
  · exact hf.trans hg.symm

/-- Both comparisons point weakly down and at least one is strict. -/
def strictComparisonPair (a b : OrderComparison) : Bool :=
  decide ((a = .less ∧ (b = .less ∨ b = .equal)) ∨ (a = .equal ∧ b = .less))

theorem strictComparisonPair_valid {a b : OrderComparison} {f g h k : ℕ → ℂ}
    (ha : a.Valid f g) (hb : b.Valid h k) (hab : strictComparisonPair a b = true) :
    f =O[atTop] g ∧ h =O[atTop] k ∧ (f =o[atTop] g ∨ h =o[atTop] k) := by
  rcases of_decide_eq_true hab with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨ha.isBigO, hb.isBigO, Or.inl ha⟩
  · exact ⟨ha.isBigO, hb.1, Or.inl ha⟩
  · exact ⟨ha.1, hb.isBigO, Or.inr hb⟩

/-- Compare `Z` forces; swapping the two coordinate comparisons gives `W`. -/
def compareForceAlgebra (cz cw cr : OrderComparison) (otherFirst otherSecond : Bool) :
    OrderComparison :=
  if strictComparisonPair cz.flip cw.flip then .less
  else if strictComparisonPair cz cr.flip then .less
  else if cw = .greater ∧ otherSecond = true then .less
  else if cz = .equal ∧ cw = .equal then .equal
  else if cz = .equal ∧ cr = .equal then .equal
  else if cw = .equal ∧ otherFirst = true ∧ otherSecond = true then .equal
  else if strictComparisonPair cz cw then .greater
  else if strictComparisonPair cz.flip cr then .greater
  else if cw = .less ∧ otherFirst = true then .greater
  else .unknown

namespace PairEstimateData

variable (p r : PairEstimateData)

theorem compare_zForce_algebra_valid (cz cw cr : OrderComparison) (a b : Bool)
    (hz : cz.Valid p.z r.z) (hw : cw.Valid p.w r.w) (hr : cr.Valid p.radius r.radius)
    (ha : a = true → r.wForce =O[atTop] p.wForce)
    (hb : b = true → p.wForce =O[atTop] r.wForce) :
    (compareForceAlgebra cz cw cr a b).Valid p.zForce r.zForce := by
  unfold compareForceAlgebra
  split_ifs with hsep hrad hcross heqsep heqrad heqcross hsep' hrad' hcross'
  · obtain ⟨hz', hw', hs⟩ := strictComparisonPair_valid hz.flip hw.flip hsep
    exact r.zForce_littleO_of_separations p hz' hw' hs
  · obtain ⟨hz', hr', hs⟩ := strictComparisonPair_valid hz hr.flip hrad
    exact p.zForce_littleO_of_z_radius r hz' hr' hs
  · exact p.zForce_littleO_of_opposite_force r (hb hcross.2)
      (by simpa only [hcross.1, OrderComparison.Valid] using hw)
  · exact p.zForce_theta_of_separations r
      (by simpa only [heqsep.1, OrderComparison.Valid] using hz)
      (by simpa only [heqsep.2, OrderComparison.Valid] using hw)
  · exact p.zForce_theta_of_z_radius r
      (by simpa only [heqrad.1, OrderComparison.Valid] using hz)
      (by simpa only [heqrad.2, OrderComparison.Valid] using hr)
  · exact p.zForce_theta_of_opposite_force r ⟨hb heqcross.2.2, ha heqcross.2.1⟩
      (by simpa only [heqcross.1, OrderComparison.Valid] using hw)
  · obtain ⟨hz', hw', hs⟩ := strictComparisonPair_valid hz hw hsep'
    exact p.zForce_littleO_of_separations r hz' hw' hs
  · obtain ⟨hz', hr', hs⟩ := strictComparisonPair_valid hz.flip hr hrad'
    exact r.zForce_littleO_of_z_radius p hz' hr' hs
  · exact r.zForce_littleO_of_opposite_force p (ha hcross'.2)
      (by simpa only [hcross'.1, OrderComparison.Valid] using hw)
  · trivial

theorem compare_wForce_algebra_valid (cz cw cr : OrderComparison) (a b : Bool)
    (hz : cz.Valid p.z r.z) (hw : cw.Valid p.w r.w) (hr : cr.Valid p.radius r.radius)
    (ha : a = true → r.zForce =O[atTop] p.zForce)
    (hb : b = true → p.zForce =O[atTop] r.zForce) :
    (compareForceAlgebra cw cz cr a b).Valid p.wForce r.wForce :=
  p.swap.compare_zForce_algebra_valid r.swap cw cz cr a b hw hz hr ha hb

/-- The reverse position/force branch in Appendix II. -/
theorem zForce_littleO_position {x : ℕ → ℂ}
    (hx : p.z =O[atTop] x) (hr : (fun _ => (1 : ℂ)) =O[atTop] p.radius)
    (hs : p.z =o[atTop] x ∨ (fun _ => (1 : ℂ)) =o[atTop] p.radius) :
    p.zForce =o[atTop] x := by
  have hi : (fun t => (p.radius t)⁻¹) =O[atTop] (fun _ => (1 : ℂ)) := by
    simpa only [inv_one] using hr.inv_rev (Eventually.of_forall fun _ h => (one_ne_zero h).elim)
  have hp : (fun t => p.z t * (p.radius t)⁻¹ ^ 3) =o[atTop] x := by
    rcases hs with h | h
    · simpa only [one_pow, mul_one] using h.mul_isBigO (hi.pow 3)
    · have hi' : (fun t => (p.radius t)⁻¹) =o[atTop] (fun _ => (1 : ℂ)) := by
        simpa only [inv_one] using h.inv_rev (Eventually.of_forall fun _ h0 => (one_ne_zero h0).elim)
      simpa only [one_pow, mul_one] using hx.mul_isLittleO (hi'.pow (by decide : 0 < 3))
  exact hp.congr (fun t => (p.zForce_radius_inverse t).symm) (fun _ => rfl)

theorem wForce_littleO_position {x : ℕ → ℂ}
    (hx : p.w =O[atTop] x) (hr : (fun _ => (1 : ℂ)) =O[atTop] p.radius)
    (hs : p.w =o[atTop] x ∨ (fun _ => (1 : ℂ)) =o[atTop] p.radius) :
    p.wForce =o[atTop] x := p.swap.zForce_littleO_position hx hr hs

end PairEstimateData

def comparePositionForceAlgebra (cx cr : OrderComparison) : OrderComparison :=
  if strictComparisonPair cx cr.flip then .less
  else if cx = .equal ∧ cr = .equal then .equal
  else if strictComparisonPair cx.flip cr then .greater
  else .unknown

namespace PairEstimateData

variable (p : PairEstimateData)

theorem compare_position_zForce_algebra_valid {x : ℕ → ℂ} (cx cr : OrderComparison)
    (hx : cx.Valid x p.z) (hr : cr.Valid (fun _ => (1 : ℂ)) p.radius) :
    (comparePositionForceAlgebra cx cr).Valid x p.zForce := by
  unfold comparePositionForceAlgebra
  split_ifs with hlt heq hgt
  · obtain ⟨hx', hr', hs⟩ := strictComparisonPair_valid hx hr.flip hlt
    exact p.position_littleO_zForce hx' hr' hs
  · exact (p.zForce_theta_position
      (show x =Θ[atTop] p.z from by simpa only [heq.1, OrderComparison.Valid] using hx).symm
      (show (fun _ => (1 : ℂ)) =Θ[atTop] p.radius from
        by simpa only [heq.2, OrderComparison.Valid] using hr).symm).symm
  · obtain ⟨hx', hr', hs⟩ := strictComparisonPair_valid hx.flip hr hgt
    exact p.zForce_littleO_position hx' hr' hs
  · trivial

theorem compare_position_wForce_algebra_valid {x : ℕ → ℂ} (cx cr : OrderComparison)
    (hx : cx.Valid x p.w) (hr : cr.Valid (fun _ => (1 : ℂ)) p.radius) :
    (comparePositionForceAlgebra cx cr).Valid x p.wForce :=
  p.swap.compare_position_zForce_algebra_valid cx cr hx hr

end PairEstimateData
end CentralConfigurations
