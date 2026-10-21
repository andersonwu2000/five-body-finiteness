import CentralConfigurations.FiveBody.D2Exceptional.GapData

namespace CentralConfigurations.FiveBody.D2.Exceptional
open scoped BigOperators
set_option maxHeartbeats 2000000

noncomputable def gapLambda (a b c x s13 s23 : ℂ) : ℂ :=
  a+b+c*(s13/x^2-s23/(x-1)^2)

noncomputable def gapEuler (a b c x s13 s23 : ℂ) : ℂ :=
  (a+c)*s13/x^2+b*(1+s23/(x-1)^2)-x*gapLambda a b c x s13 s23

noncomputable def gapTrace (a b c x s13 s23 : ℂ) : ℂ :=
  (a+b)+(a+c)*s13/x^3+(b+c)*s23/(x-1)^3

theorem force_difference01 {mass : Fin 3 → ℂ} (r : ZWSystem ℂ 3 mass) :
    r.w 1-r.w 0 = (mass 0+mass 1)*r.delta 0 1^3*(r.w 1-r.w 0)+
      mass 2*r.delta 1 2^3*(r.w 1-r.w 2)-mass 2*r.delta 0 2^3*(r.w 0-r.w 2) := by
  have h0 := r.force_w 0
  have h1 := r.force_w 1
  simp [Fin.sum_univ_succ,r.delta_symm 1 0] at h0 h1
  linear_combination h1-h0

theorem force_difference02 {mass : Fin 3 → ℂ} (r : ZWSystem ℂ 3 mass) :
    r.w 2-r.w 0 = (mass 0+mass 2)*r.delta 0 2^3*(r.w 2-r.w 0)+
      mass 1*r.delta 1 2^3*(r.w 2-r.w 1)-mass 1*r.delta 0 1^3*(r.w 0-r.w 1) := by
  have h0 := r.force_w 0
  have h2 := r.force_w 2
  simp [Fin.sum_univ_succ,r.delta_symm 2 0,r.delta_symm 2 1] at h0 h2
  linear_combination h2-h0

theorem GapData.original_rows {mass : Fin 3 → ℂ} {r : ZWSystem ℂ 3 mass} (d : GapData r) :
    d.lam = gapLambda (mass 0) (mass 1) (mass 2) d.x d.sign13 d.sign23 ∧
    d.lam*d.x = (mass 0+mass 2)*d.sign13/d.x^2+
      mass 1*(1+d.sign23/(d.x-1)^2) := by
  have hg01 := d.difference01
  have hg02 := d.difference02
  have hw12 : r.w 1-r.w 2 = d.scale*(1-d.x) := by linear_combination hg01-hg02
  have hw20 : r.w 0-r.w 2 = -d.scale*d.x := by linear_combination -hg02
  have hw21 : r.w 2-r.w 1 = d.scale*(d.x-1) := by linear_combination hg02-hg01
  have hw10 : r.w 0-r.w 1 = -d.scale := by linear_combination -hg01
  have hcoef1 : (mass 0+mass 1)*r.delta 0 1^3+
      mass 2*d.x*r.delta 0 2^3+mass 2*(1-d.x)*r.delta 1 2^3 = 1 := by
    apply mul_left_cancel₀ d.scale_ne_zero
    have h := force_difference01 r
    rw [hg01,hw12,hw20] at h
    linear_combination -h
  have hcoef2 : (mass 0+mass 2)*d.x*r.delta 0 2^3+
      mass 1*r.delta 0 1^3+mass 1*(d.x-1)*r.delta 1 2^3 = d.x := by
    apply mul_left_cancel₀ d.scale_ne_zero
    have h := force_difference02 r
    rw [hg02,hw21,hw10] at h
    linear_combination -h
  have he1 : d.lam*((mass 0+mass 1)*r.delta 0 1^3+
      mass 2*d.x*r.delta 0 2^3+mass 2*(1-d.x)*r.delta 1 2^3) =
      gapLambda (mass 0) (mass 1) (mass 2) d.x d.sign13 d.sign23 := by
    rw [d.cube01,d.cube02,d.cube12]
    dsimp [gapLambda]
    field_simp [d.lam_ne_zero,d.x_ne_zero,sub_ne_zero.mpr d.x_ne_one]
    ring
  have he2 : d.lam*((mass 0+mass 2)*d.x*r.delta 0 2^3+
      mass 1*r.delta 0 1^3+mass 1*(d.x-1)*r.delta 1 2^3) =
      (mass 0+mass 2)*d.sign13/d.x^2+mass 1*(1+d.sign23/(d.x-1)^2) := by
    rw [d.cube01,d.cube02,d.cube12]
    field_simp [d.lam_ne_zero,d.x_ne_zero,sub_ne_zero.mpr d.x_ne_one]
    ring
  rw [hcoef1,mul_one] at he1
  rw [hcoef2] at he2
  exact ⟨he1,he2⟩

theorem GapData.euler_zero {mass : Fin 3 → ℂ} {r : ZWSystem ℂ 3 mass} (d : GapData r) :
    gapEuler (mass 0) (mass 1) (mass 2) d.x d.sign13 d.sign23=0 := by
  obtain ⟨h1,h2⟩ := d.original_rows
  dsimp [gapEuler]
  rw [← h1]
  linear_combination -h2

theorem GapData.trace_zero {mass : Fin 3 → ℂ} {r : ZWSystem ℂ 3 mass} (d : GapData r)
    (hell : transverseEigenvalue r=0) :
    gapTrace (mass 0) (mass 1) (mass 2) d.x d.sign13 d.sign23-
      gapLambda (mass 0) (mass 1) (mass 2) d.x d.sign13 d.sign23 = 0 := by
  have ht := d.trace
  change transverseEigenvalue r =
    gapTrace (mass 0) (mass 1) (mass 2) d.x d.sign13 d.sign23/d.lam-1 at ht
  rw [hell] at ht
  field_simp [d.lam_ne_zero] at ht
  rw [← d.original_rows.1]
  linear_combination -ht

end CentralConfigurations.FiveBody.D2.Exceptional
