import CentralConfigurations.FiveBody.D6Butterfly.WingCatalogue
import CentralConfigurations.FiveBody.PhysicalPotentialFloor
import CentralConfigurations.Algebra.DisconnectedPairMass

namespace CentralConfigurations.FiveBody.D8

theorem lower_energy_cube_bound {a p I0 : ℝ} (ha : 0<a) (hp : 0<p)
    {E F G : ℂ} (hE : E≠0) (hF : F≠0) (hG : G≠0)
    (hFG : F^3=G^3) (hclosure : E⁻¹^2-2*F⁻¹^2-2*G⁻¹^2=0)
    (hforce : 2*(a:ℂ)*E^3+((p:ℂ)/4)*F^3=1)
    (henergy : (I0:ℂ)=(a:ℂ)*F⁻¹^2+a*G⁻¹^2) :
    I0^3≤a^3*(a+p)^2/2 := by
  let k := F^3/E^3
  have hk : k^2=64 ∨ k^2= -8 := D6.wing_reciprocal_catalogue hE hF hG hFG hclosure
  have hI : (I0:ℂ)=(a:ℂ)/2*E⁻¹^2 := by linear_combination henergy-(a:ℂ)/2*hclosure
  have hEcube : E⁻¹^3=2*(a:ℂ)+(p:ℂ)/4*k := by
    dsimp [k]
    field_simp [hE]
    linear_combination -4*hforce
  have hcube : (I0:ℂ)^3=(a:ℂ)^3/8*(2*(a:ℂ)+(p:ℂ)/4*k)^2 := by
    rw [hI,← hEcube]
    ring
  rcases hk with hk|hk
  · have hk' : k=8 ∨ k= -8 := eq_or_eq_neg_of_sq_eq_sq k 8 (by norm_num; exact hk)
    rcases hk' with hk'|hk'
    · have hh : (I0:ℂ)^3=((a^3*(a+p)^2/2:ℝ):ℂ) := by
        rw [hk'] at hcube
        push_cast
        linear_combination hcube
      have hr : I0^3=a^3*(a+p)^2/2 := by exact_mod_cast hh
      exact hr.le
    · have hh : (I0:ℂ)^3=((a^3*(a-p)^2/2:ℝ):ℂ) := by
        rw [hk'] at hcube
        push_cast
        linear_combination hcube
      have hr : I0^3=a^3*(a-p)^2/2 := by exact_mod_cast hh
      rw [hr]
      have hpos : 0<a^4*p := mul_pos (pow_pos ha 4) hp
      nlinarith
  · obtain ⟨hkr,hki⟩ := complex_square_negative_real (by norm_num : (0:ℝ)<8) (by simpa using hk)
    have he : (I0:ℂ)^3=(a:ℂ)^3/8*(4*(a:ℂ)^2+(a:ℂ)*p*k-(p:ℂ)^2/2) := by
      linear_combination hcube+((a:ℂ)^3*p^2/128)*hk
    have hi := congrArg Complex.im he
    simp [← Complex.ofReal_pow,Complex.mul_im,Complex.sub_im,Complex.add_im,hkr] at hi
    have hn : k.im≠0 := by intro hz; rw [hz] at hki; norm_num at hki
    simp_all [ne_of_gt ha,ne_of_gt hp]

theorem strict_lower_energy_gap {a p : ℝ} (ha : 0<a) (hp : 0<p) :
    (2*a+9*p/4)*(a^3*(a+p)^2/2)<(a^2+(9/2:ℝ)*p*a+(3/2:ℝ)*p^2)^3 := by
  have he : (a^2+(9/2:ℝ)*p*a+(3/2:ℝ)*p^2)^3-(2*a+9*p/4)*(a^3*(a+p)^2/2)=
      (83*p*a^5+496*p^2*a^4+1044*p^3*a^3+783*p^4*a^2+243*p^5*a+27*p^6)/8 := by ring
  have hp : 0<(83*p*a^5+496*p^2*a^4+1044*p^3*a^3+783*p^4*a^2+243*p^5*a+27*p^6)/8 := by positivity
  linarith

theorem lower_energy_impossible {m : Fin 5 → ℝ} {I0 : ℝ} (hm : ∀ i, 0<m i)
    (heq : m 2=m 3) (hab : m 0=m 1) (hc : m 4=m 2/4)
    (hphysical : PhysicalPotentialLevel m I0)
    {E F G : ℂ} (hE : E≠0) (hF : F≠0) (hG : G≠0)
    (hFG : F^3=G^3) (hclosure : E⁻¹^2-2*F⁻¹^2-2*G⁻¹^2=0)
    (hforce : 2*(m 0:ℂ)*E^3+(m 4:ℂ)*F^3=1)
    (henergy : (I0:ℂ)=(m 0:ℂ)*F⁻¹^2+m 0*G⁻¹^2) : False := by
  have hforce' : 2*(m 0:ℂ)*E^3+((m 2:ℂ)/4)*F^3=1 := by
    simpa only [hc,Complex.ofReal_div,Complex.ofReal_ofNat] using hforce
  have hbound := lower_energy_cube_bound (hm 0) (hm 2) hE hF hG hFG hclosure hforce' henergy
  have hgap := strict_lower_energy_gap (hm 0) (hm 2)
  have hM : totalMass m=2*m 0+9*m 2/4 := by
    simp [totalMass,Fin.sum_univ_succ,← hab,← heq,hc]
    ring
  have hS : pairMassSum m=m 0^2+(9/2:ℝ)*m 2*m 0+(3/2:ℝ)*m 2^2 := by
    simp [pairMassSum,Fin.sum_univ_succ,← hab,← heq,hc]
    ring
  have hfloor := hphysical.2
  rw [hM,hS] at hfloor
  have hpos : 0≤2*m 0+9*m 2/4 := by have h0 := hm 0; have h2 := hm 2; positivity
  have hh := mul_le_mul_of_nonneg_left hbound hpos
  linarith

end CentralConfigurations.FiveBody.D8
