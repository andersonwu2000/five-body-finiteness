import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

namespace CentralConfigurations.FiveBody.D2.Exceptional

theorem hermitian_re_lower (x y : ℂ) : -‖x‖*‖y‖ ≤ (x*star y).re := by
  have h := neg_le_neg (Complex.re_le_norm (-(x*star y)))
  simpa [norm_mul] using h

theorem same_disk_positive {h U V : ℂ} (hD : 6 < ‖h‖) (hU : ‖U‖ ≤ 2) (hV : ‖V‖ ≤ 2) :
    0 < ((h+U)*star (h+V)).re := by
  have hHH : (h*star h).re = ‖h‖^2 := by
    simpa [Complex.star_def,pow_two,Complex.mul_re] using congrArg Complex.re (Complex.mul_conj' h)
  have hex : ((h+U)*star (h+V)).re = ‖h‖^2+(h*star V).re+(U*star h).re+(U*star V).re := by
    rw [star_add,add_mul,mul_add,mul_add]
    simp only [Complex.add_re,hHH]
    ring
  have h1 := hermitian_re_lower h V
  have h2 := hermitian_re_lower U h
  have h3 := hermitian_re_lower U V
  have hb1 := mul_le_mul_of_nonneg_left hV (norm_nonneg h)
  have hb2 := mul_le_mul_of_nonneg_right hU (norm_nonneg h)
  have hb3 : ‖U‖*‖V‖ ≤ 4 := by
    have h := mul_le_mul hU hV (norm_nonneg V) (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at h ⊢
    exact h
  have hp : 0 < (‖h‖-6)*(‖h‖+2) := mul_pos (by linarith) (by linarith)
  rw [hex]
  nlinarith

theorem signed_heavy_not_orthogonal {h U V σ τ : ℂ}
    (hσ : σ=1 ∨ σ=-1) (hτ : τ=1 ∨ τ=-1)
    (hD : 6 < ‖h‖) (hU : ‖U‖ ≤ 2) (hV : ‖V‖ ≤ 2) :
    ((σ*h+U)*star (τ*h+V)).re ≠ 0 := by
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
  · simpa using ne_of_gt (same_disk_positive hD hU hV)
  · have hpos := same_disk_positive hD hU (by simpa only [norm_neg] using hV : ‖-V‖ ≤ 2)
    have he : ((h+U)*star (-h+V)).re = -((h+U)*star (h+(-V))).re := by
      rw [show -h+V = -(h+(-V)) by ring,star_neg,mul_neg,Complex.neg_re]
    simpa only [one_mul,neg_one_mul,he] using neg_ne_zero.mpr (ne_of_gt hpos)
  · have hpos := same_disk_positive hD (by simpa only [norm_neg] using hU : ‖-U‖ ≤ 2) hV
    have he : ((-h+U)*star (h+V)).re = -((h+(-U))*star (h+V)).re := by
      rw [show -h+U = -(h+(-U)) by ring,neg_mul,Complex.neg_re]
    simpa only [one_mul,neg_one_mul,he] using neg_ne_zero.mpr (ne_of_gt hpos)
  · have hpos := same_disk_positive hD (by simpa only [norm_neg] using hU : ‖-U‖ ≤ 2)
      (by simpa only [norm_neg] using hV : ‖-V‖ ≤ 2)
    have he : ((-h+U)*star (-h+V)).re = ((h+(-U))*star (h+(-V))).re := by
      congr 1
      rw [show -h+U = -(h+(-U)) by ring,show -h+V = -(h+(-V)) by ring,star_neg,neg_mul_neg]
    simpa only [neg_one_mul,he] using ne_of_gt hpos

theorem orthogonal_of_original_torque {A C : ℂ} {t : ℝ}
    (htorque : (t : ℂ)*A+Complex.I*C=0) : (A*star C).re = 0 := by
  have hI : Complex.I^2+1=0 := by simp
  have hC : C=Complex.I*(t : ℂ)*A := by
    linear_combination -Complex.I*htorque+C*hI
  have he : A*star C = -Complex.I*(t : ℂ)*(A*star A) := by
    rw [hC]
    simp only [star_mul]
    simp
    ring
  rw [he,show A*star A = (‖A‖^2 : ℝ) by simpa [Complex.star_def] using Complex.mul_conj' A]
  simp [pow_two]

theorem false_of_signed_heavy_torque {h U V σ τ : ℂ} {t : ℝ}
    (hσ : σ=1 ∨ σ=-1) (hτ : τ=1 ∨ τ=-1)
    (hD : 6 < ‖h‖) (hU : ‖U‖ ≤ 2) (hV : ‖V‖ ≤ 2)
    (htorque : (t : ℂ)*(σ*h+U)+Complex.I*(τ*h+V)=0) : False :=
  signed_heavy_not_orthogonal hσ hτ hD hU hV (orthogonal_of_original_torque htorque)

end CentralConfigurations.FiveBody.D2.Exceptional
