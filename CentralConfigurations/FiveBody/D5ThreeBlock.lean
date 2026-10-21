import CentralConfigurations.Model.ZWMassCenter
import Mathlib.Tactic.LinearCombination

namespace CentralConfigurations.FiveBody.D5

/-- A zero block in both colors forces a zero color in a centered, null
three-block configuration. Only the indicated fixed mass factors are divided. -/
theorem null_centered_zero_block {K p q a b c d e f : ℂ}
    (hp : p ≠ 0) (hq : q ≠ 0) (hpq : p + q ≠ 0)
    (hz : K*a+p*b+q*c = 0) (hw : K*d+p*e+q*f = 0)
    (hI : K*a*d+p*b*e+q*c*f = 0) (ha : a = 0) (hd : d = 0) :
    (a = 0 ∧ b = 0 ∧ c = 0) ∨ (d = 0 ∧ e = 0 ∧ f = 0) := by
  subst a; subst d
  have hbe : p * (p+q) * (b*e) = 0 := by
    linear_combination q*hI - (q*f)*hz + (p*b)*hw
  have hprod : b*e = 0 := (mul_eq_zero.mp hbe).resolve_left (mul_ne_zero hp hpq)
  rcases mul_eq_zero.mp hprod with hb | he
  · left
    refine ⟨rfl,hb,?_⟩
    simpa [hb,hq] using hz
  · right
    refine ⟨rfl,he,?_⟩
    simpa [he,hq] using hw

/-- The compact limit used for D5: three centered blocks cannot have null
inertia and two nonzero colors when every metrically isolated block has
vanishing force. This finite statement retains complex signed metrics. -/
theorem three_block_null_impossible {K p q a b c d e f : ℂ}
    (hK : K ≠ 0) (hp : p ≠ 0) (hq : q ≠ 0)
    (hKp : K+p ≠ 0) (hKq : K+q ≠ 0) (hpq : p+q ≠ 0)
    (hM : K+p+q ≠ 0)
    (hz : K*a+p*b+q*c = 0) (hw : K*d+p*e+q*f = 0)
    (hI : K*a*d+p*b*e+q*c*f = 0)
    (hzn : ¬ (a = 0 ∧ b = 0 ∧ c = 0))
    (hwn : ¬ (d = 0 ∧ e = 0 ∧ f = 0))
    (h0 : (a-b)*(d-e) ≠ 0 → (a-c)*(d-f) ≠ 0 → a=0 ∧ d=0)
    (h1 : (a-b)*(d-e) ≠ 0 → (b-c)*(e-f) ≠ 0 → b=0 ∧ e=0)
    (h2 : (a-c)*(d-f) ≠ 0 → (b-c)*(e-f) ≠ 0 → c=0 ∧ f=0) : False := by
  have pair : K*p*((a-b)*(d-e)) + K*q*((a-c)*(d-f)) +
      p*q*((b-c)*(e-f)) = 0 := by
    linear_combination (K+p+q)*hI - (K*d+p*e+q*f)*hz
  have no0 : ¬ (a=0 ∧ d=0) := by
    intro h
    exact (null_centered_zero_block hp hq hpq hz hw hI h.1 h.2).elim hzn hwn
  have no1 : ¬ (b=0 ∧ e=0) := by
    intro h
    have hh := null_centered_zero_block hK hq hKq
      (show p*b+K*a+q*c=0 by linear_combination hz)
      (show p*e+K*d+q*f=0 by linear_combination hw)
      (show p*b*e+K*a*d+q*c*f=0 by linear_combination hI) h.1 h.2
    exact hh.elim (fun h => hzn ⟨h.2.1,h.1,h.2.2⟩) (fun h => hwn ⟨h.2.1,h.1,h.2.2⟩)
  have no2 : ¬ (c=0 ∧ f=0) := by
    intro h
    have hh := null_centered_zero_block hK hp hKp
      (show q*c+K*a+p*b=0 by linear_combination hz)
      (show q*f+K*d+p*e=0 by linear_combination hw)
      (show q*c*f+K*a*d+p*b*e=0 by linear_combination hI) h.1 h.2
    exact hh.elim (fun h => hzn ⟨h.2.1,h.2.2,h.1⟩) (fun h => hwn ⟨h.2.1,h.2.2,h.1⟩)
  have ab : (a-b)*(d-e) = 0 := by
    by_contra hab
    have hac : (a-c)*(d-f)=0 := by by_contra h; exact no0 (h0 hab h)
    have hbc : (b-c)*(e-f)=0 := by by_contra h; exact no1 (h1 hab h)
    simpa [hac,hbc,hK,hp,hab] using pair
  have ac : (a-c)*(d-f) = 0 := by
    by_contra hac
    have hbc : (b-c)*(e-f)=0 := by by_contra h; exact no2 (h2 hac h)
    simpa [ab,hbc,hK,hq,hac] using pair
  have bc : (b-c)*(e-f) = 0 := by
    simpa [ab,ac,hp,hq] using pair
  have samez : a=b → a=c → False := by
    intro hab hac
    have h : (K+p+q)*a=0 := by linear_combination hz + p*(hab) + q*(hac)
    have ha := (mul_eq_zero.mp h).resolve_left hM
    exact hzn ⟨ha,hab ▸ ha,hac ▸ ha⟩
  have samew : d=e → d=f → False := by
    intro hde hdf
    have h : (K+p+q)*d=0 := by linear_combination hw + p*(hde) + q*(hdf)
    have hd := (mul_eq_zero.mp h).resolve_left hM
    exact hwn ⟨hd,hde ▸ hd,hdf ▸ hd⟩
  rcases mul_eq_zero.mp ab with hab | hde
  · have hab := sub_eq_zero.mp hab
    rcases mul_eq_zero.mp ac with hac | hdf
    · exact samez hab (sub_eq_zero.mp hac)
    · rcases mul_eq_zero.mp bc with hbc | hef
      · exact samez hab (hab.trans (sub_eq_zero.mp hbc))
      · exact samew ((sub_eq_zero.mp hdf).trans (sub_eq_zero.mp hef).symm) (sub_eq_zero.mp hdf)
  · have hde := sub_eq_zero.mp hde
    rcases mul_eq_zero.mp ac with hac | hdf
    · rcases mul_eq_zero.mp bc with hbc | hef
      · exact samez ((sub_eq_zero.mp hac).trans (sub_eq_zero.mp hbc).symm) (sub_eq_zero.mp hac)
      · exact samew hde (hde.trans (sub_eq_zero.mp hef))
    · exact samew hde (sub_eq_zero.mp hdf)

end CentralConfigurations.FiveBody.D5
