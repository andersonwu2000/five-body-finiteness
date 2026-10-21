import CentralConfigurations.FiveBody.D2Resonance.PositiveFactor

noncomputable section
open Polynomial
namespace CentralConfigurations.FiveBody.D2.Resonance
open Exceptional
set_option maxHeartbeats 2000000

structure PositiveRepeatedCase (a b c : ℝ) (x : ℂ) : Prop where
  equal_mass : a=c
  heavy_mass : b=(2+2*Real.sqrt 2)*a
  twice_re : 2*x.re=Real.sqrt 2-1
  norm_sq : Complex.normSq x=Real.sqrt 2-1
  quadratic : x^2-((Real.sqrt 2-1:ℝ):ℂ)*x+((Real.sqrt 2-1:ℝ):ℂ)=0

theorem realPair_quadratic_root (x : ℂ) :
    x^2-((2*x.re:ℝ):ℂ)*x+(Complex.normSq x:ℂ)=0 := by
  apply Complex.ext <;> simp [Complex.normSq,pow_two]
  all_goals ring

theorem positive_repeated_classification (a b c : ℝ) (x : ℂ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c)
    (hroot : (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) 1 1).eval x=0)
    (hderiv : (gapPolynomial (a:ℂ) (b:ℂ) (c:ℂ) 1 1).derivative.eval x=0) :
    PositiveRepeatedCase a b c x := by
  obtain ⟨r,hr,hf⟩ := positive_repeated_factor a b c x ha hb hc hroot hderiv
  have hm : a+b≠0 := ne_of_gt (by linarith)
  have hfn := positive_normalized_factor a b c x r hm hf
  have hab : a/(a+b)+b/(a+b)=1 := by rw [← add_div,div_self hm]
  have hx := positive_quintic_repeated_nonreal a b c x ha hb hc hroot hderiv
  have hvpos : 0<Complex.normSq x := Complex.normSq_pos.mpr (by
    intro he
    exact hx (by simp [he]))
  change gapPolynomial (a/(a+b)) (b/(a+b)) (c/(a+b)) 1 1 =
    -(X^2-C (2*x.re)*X+C (Complex.normSq x))^2*(X-C r) at hfn
  obtain ⟨h1,h2,h3⟩ := coefficient_ideal_of_factor _ _ _ _ _ _ hab hfn
  obtain ⟨hr2,hu,hv⟩ := coefficient_positive_fiber hr hvpos h1 h2 h3
  obtain ⟨hA,hC⟩ := normalized_mass_rows_of_factor _ _ _ _ _ _ hab hfn
  rw [hr2,hu] at hA
  rw [hr2,hv] at hC
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hCA : c/(a+b)=a/(a+b) := by nlinarith
  have hBA : b/(a+b)=(2+2*Real.sqrt 2)*(a/(a+b)) := by
    calc
      b/(a+b)=1-a/(a+b) := by linarith
      _ = _ := by rw [hA]; nlinarith
  have hac : a=c := (div_left_inj' hm).mp hCA.symm
  have hba : b=(2+2*Real.sqrt 2)*a := by
    apply (div_left_inj' hm).mp
    calc
      b/(a+b)=(2+2*Real.sqrt 2)*(a/(a+b)) := hBA
      _ = ((2+2*Real.sqrt 2)*a)/(a+b) := by ring
  have hquad := realPair_quadratic_root x
  rw [hu,hv] at hquad
  exact ⟨hac,hba,hu,hv,hquad⟩

end CentralConfigurations.FiveBody.D2.Resonance
