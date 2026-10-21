import CentralConfigurations.FiveBody.D2Resonance.RealRoot
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.RingTheory.Coprime.Lemmas

noncomputable section
open Polynomial
namespace CentralConfigurations.FiveBody.D2.Resonance
set_option maxHeartbeats 2000000

def realPairQuadratic (x : ℂ) : ℝ[X] :=
  X^2-C (2*x.re)*X+C (Complex.normSq x)

theorem realPairQuadratic_monic (x : ℂ) : (realPairQuadratic x).Monic := by
  dsimp [realPairQuadratic]
  monicity <;> omega

theorem realPairQuadratic_natDegree (x : ℂ) : (realPairQuadratic x).natDegree=2 := by
  dsimp [realPairQuadratic]
  compute_degree!

theorem realPairQuadratic_map (x : ℂ) :
    (realPairQuadratic x).map Complex.ofRealHom =
      (X-C x)*(X-C (star x)) := by
  simp only [realPairQuadratic,Polynomial.map_add,Polynomial.map_sub,
    Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
  have hs : (2*x.re:ℂ)=x+star x := by
    apply Complex.ext <;> simp
    all_goals ring
  have hp : (Complex.normSq x:ℂ)=x*star x := by
    apply Complex.ext <;> simp [Complex.normSq]
    all_goals ring
  change X^2-C ((2*x.re:ℝ):ℂ)*X+C (Complex.normSq x:ℂ) = _
  simp only [Complex.ofReal_mul,Complex.ofReal_ofNat]
  rw [hs,hp,map_add,map_mul]
  ring

theorem real_polynomial_conjugate_eval (p : ℝ[X]) (x : ℂ) :
    (p.map Complex.ofRealHom).eval (star x) =
      star ((p.map Complex.ofRealHom).eval x) := by
  have hmap : (p.map Complex.ofRealHom).map (starRingEnd ℂ) = p.map Complex.ofRealHom := by
    rw [map_map]
    congr 1
    ext r
    simp
  conv_lhs => rw [← hmap]
  exact eval_map_apply (starRingEnd ℂ) x

theorem real_polynomial_conjugate_derivative_eval (p : ℝ[X]) (x : ℂ) :
    (p.map Complex.ofRealHom).derivative.eval (star x) =
      star ((p.map Complex.ofRealHom).derivative.eval x) := by
  rw [derivative_map]
  exact real_polynomial_conjugate_eval p.derivative x

theorem realPairQuadratic_sq_dvd (p : ℝ[X]) (hp : p≠0) (x : ℂ) (hx : x.im≠0)
    (hroot : (p.map Complex.ofRealHom).eval x=0)
    (hderiv : (p.map Complex.ofRealHom).derivative.eval x=0) :
    (realPairQuadratic x)^2 ∣ p := by
  have hpn : p.map Complex.ofRealHom≠0 := map_ne_zero hp
  have hconj : x≠star x := by
    intro he
    have hi := congrArg Complex.im he
    simp at hi
    exact hx (by linarith)
  have hxmul : 2 ≤ (p.map Complex.ofRealHom).rootMultiplicity x := by
    have := (one_lt_rootMultiplicity_iff_isRoot hpn).mpr ⟨hroot,hderiv⟩
    omega
  have hcxmul : 2 ≤ (p.map Complex.ofRealHom).rootMultiplicity (star x) := by
    have hr : (p.map Complex.ofRealHom).eval (star x)=0 := by
      rw [real_polynomial_conjugate_eval,hroot,star_zero]
    have hd : (p.map Complex.ofRealHom).derivative.eval (star x)=0 := by
      rw [real_polynomial_conjugate_derivative_eval,hderiv,star_zero]
    have := (one_lt_rootMultiplicity_iff_isRoot hpn).mpr ⟨hr,hd⟩
    omega
  have hd1 : (X-C x)^2 ∣ p.map Complex.ofRealHom :=
    (le_rootMultiplicity_iff hpn).mp hxmul
  have hd2 : (X-C (star x))^2 ∣ p.map Complex.ofRealHom :=
    (le_rootMultiplicity_iff hpn).mp hcxmul
  have hc : IsCoprime (X-C x) (X-C (star x)) :=
    isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.mpr hconj).isUnit
  have hd := (hc.pow (m:=2) (n:=2)).mul_dvd hd1 hd2
  rw [← mul_pow,← realPairQuadratic_map,← Polynomial.map_pow] at hd
  exact (map_dvd_map Complex.ofRealHom Complex.ofReal_injective
    ((realPairQuadratic_monic x).pow 2)).mp hd

theorem quintic_conjugate_factor (p : ℝ[X]) (hpdeg : p.natDegree=5)
    (L : ℝ) (hL : p.leadingCoeff=L) (x : ℂ) (hx : x.im≠0)
    (hroot : (p.map Complex.ofRealHom).eval x=0)
    (hderiv : (p.map Complex.ofRealHom).derivative.eval x=0) :
    ∃ r : ℝ, p=C L*(realPairQuadratic x)^2*(X-C r) := by
  have hp : p≠0 := ne_zero_of_natDegree_gt (show 0<p.natDegree by omega)
  have hLn : L≠0 := hL ▸ leadingCoeff_ne_zero.mpr hp
  obtain ⟨s,hs⟩ := realPairQuadratic_sq_dvd p hp x hx hroot hderiv
  have hsne : s≠0 := by intro he; rw [he,mul_zero] at hs; exact hp hs
  have hqd : ((realPairQuadratic x)^2).natDegree=4 := by
    rw [natDegree_pow,realPairQuadratic_natDegree]
  have hsd : s.natDegree=1 := by
    have := natDegree_mul (pow_ne_zero 2 (realPairQuadratic_monic x).ne_zero) hsne
    rw [← hs,hpdeg,hqd] at this
    omega
  have hsc : s.coeff 1=L := by
    have hlead := congrArg leadingCoeff hs
    rw [leadingCoeff_mul,(realPairQuadratic_monic x |>.pow 2).leadingCoeff,one_mul,hL] at hlead
    simpa only [leadingCoeff,hsd] using hlead.symm
  have hseq : s=C L*X+C (s.coeff 0) := by
    simpa [hsc] using eq_X_add_C_of_natDegree_le_one hsd.le
  let r := -s.coeff 0/L
  have hr : L*r= -s.coeff 0 := by dsimp [r]; field_simp
  refine ⟨r,?_⟩
  rw [hs,hseq]
  have hc : C L*C r= -C (s.coeff 0) := by rw [← map_mul,hr,map_neg]
  linear_combination ((realPairQuadratic x)^2)*hc

end CentralConfigurations.FiveBody.D2.Resonance
