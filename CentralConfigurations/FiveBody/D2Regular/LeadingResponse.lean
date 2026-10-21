import CentralConfigurations.FiveBody.D2Regular.WeightedPlane
import CentralConfigurations.FiveBody.D2Regular.Chart
import CentralConfigurations.FiveBody.D2HZero.Extraction

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000

def centeredVector (n v : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  v i-weightedCenter n v/(n 0+n 1+n 2)

theorem centeredVector_center (n v : Fin 3 → ℂ) (hB : n 0+n 1+n 2≠0) :
    weightedCenter n (centeredVector n v)=0 := by
  dsimp [weightedCenter,centeredVector]
  simp [Fin.sum_univ_succ]
  field_simp [hB]
  ring

theorem centeredVector_smul (n v : Fin 3 → ℂ) (a : ℂ) (i : Fin 3) :
    centeredVector n (fun j => a*v j) i=a*centeredVector n v i := by
  dsimp [centeredVector,weightedCenter]
  simp [Fin.sum_univ_succ]
  ring

theorem centeredVector_orthogonal (n d B : Fin 3 → ℂ) (hd : ∀ i, d i≠0)
    (hc : weightedCenter n d=0) (hB : weightedCenter n B=0) :
    bilinear n d (centeredVector n (fun i => B i/d i))=0 := by
  let K := weightedCenter n (fun i => B i/d i)/(n 0+n 1+n 2)
  have he (i : Fin 3) : n i*d i*centeredVector n (fun i => B i/d i) i=
      n i*B i-K*(n i*d i) := by
    dsimp [centeredVector]
    change n i*d i*(B i/d i-K)=_
    field_simp [hd i]
  dsimp [bilinear]
  simp_rw [he]
  rw [Finset.sum_sub_distrib,← Finset.mul_sum]
  change weightedCenter n B-K*weightedCenter n d=0
  rw [hB,hc,mul_zero,sub_zero]

theorem original_response_centered {m : Fin 5 → ℝ}
    (s : FiveBodySource18Certificate m) (hm : ∀ i, 0<m i) :
    weightedCenter (fun i : Fin 3 => (m (tripleIndex i):ℂ)) (HZero.centeredCrossResponse s)=0 := by
  have hB : (m 0:ℂ)+m 1+m 2≠0 := by
    exact_mod_cast ne_of_gt (add_pos (add_pos (hm 0) (hm 1)) (hm 2))
  simpa [centeredVector,HZero.centeredCrossResponse,weightedCenter,Fin.sum_univ_succ,tripleIndex,add_assoc]
    using centeredVector_center (fun i : Fin 3 => (m (tripleIndex i):ℂ))
      (HZero.crossResponse s) hB

theorem original_response_orthogonal {m : Fin 5 → ℝ}
    (s : FiveBodySource18Certificate m) :
    bilinear (fun i : Fin 3 => (m (tripleIndex i):ℂ)) s.triangle.w (HZero.centeredCrossResponse s)=0 := by
  have hB : weightedCenter (fun i : Fin 3 => (m (tripleIndex i):ℂ)) (HZero.crossCombination s)=0 := by
    have hh := s.cross_torque
    simp [weightedCenter,HZero.crossCombination,Fin.sum_univ_succ,tripleIndex] at hh ⊢
    linear_combination hh
  have he : centeredVector (fun i : Fin 3 => (m (tripleIndex i):ℂ))
      (fun i => HZero.crossCombination s i/s.triangle.w i)=HZero.centeredCrossResponse s := by
    funext i
    simp [centeredVector,HZero.centeredCrossResponse,HZero.crossResponse,weightedCenter,
      Fin.sum_univ_succ,tripleIndex,add_assoc]
  rw [← he]
  exact centeredVector_orthogonal (fun i : Fin 3 => (m (tripleIndex i):ℂ)) s.triangle.w
    (HZero.crossCombination s) s.w_ne_zero s.triangle.mass_center_w hB

/-- The actual response has nonzero complex bilinear norm, using the already
proved physical H=0 deletion and the exact transverse one-dimensionality. -/
theorem original_response_norm_ne {m : Fin 5 → ℝ}
    {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
    {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
    (s : PhysicalEulerLimit m q l I0) (hm : ∀ i, 0<m i) :
    bilinear (fun i : Fin 3 => (m (tripleIndex i):ℂ))
      (HZero.centeredCrossResponse s.toFiveBodySource18Certificate)
      (HZero.centeredCrossResponse s.toFiveBodySource18Certificate)≠0 := by
  intro hh
  apply HZero.PhysicalEulerLimit.not_centered_response_zero s hm
  apply transverse_no_isotropic (fun i : Fin 3 => (m (tripleIndex i):ℂ)) s.triangle.w
    (HZero.centeredCrossResponse s.toFiveBodySource18Certificate)
    (fun i => Complex.ofReal_ne_zero.mpr (ne_of_gt (hm (tripleIndex i)))) ?_
    (s.triangle.w_separation_ne_zero (by decide)) s.triangle.mass_center_w ?_
    (original_response_centered s.toFiveBodySource18Certificate hm)
    (original_response_orthogonal s.toFiveBodySource18Certificate) hh
  · change (m 0:ℂ)+m 1+m 2≠0
    exact_mod_cast ne_of_gt (add_pos (add_pos (hm 0) (hm 1)) (hm 2))
  · simpa only [bilinear,pow_two,mul_assoc] using s.nonisotropic

theorem response_gauge_transport {m : Fin 5 → ℝ}
    (s : FiveBodySource18Certificate m) {gamma w2 : ℂ} (hg : gamma≠0) (hw : w2≠0)
    (i : Fin 3) :
    centeredVector (fun j : Fin 3 => (m (tripleIndex j):ℂ))
      (fun j => ((m 3:ℂ)*(s.cross 0 j/gamma)+m 4*(s.cross 1 j/gamma))/(s.triangle.w j/w2)) i=
      (w2/gamma)*HZero.centeredCrossResponse s i := by
  have he (j : Fin 3) :
      ((m 3:ℂ)*(s.cross 0 j/gamma)+m 4*(s.cross 1 j/gamma))/(s.triangle.w j/w2)=
      (w2/gamma)*HZero.crossResponse s j := by
    dsimp [HZero.crossResponse,HZero.crossCombination]
    field_simp [hg,hw,s.w_ne_zero j]
  simp_rw [he]
  rw [centeredVector_smul]
  congr 1
  simp [centeredVector,HZero.centeredCrossResponse,weightedCenter,Fin.sum_univ_succ,tripleIndex,add_assoc]

end
end CentralConfigurations.FiveBody.D2.Regular
