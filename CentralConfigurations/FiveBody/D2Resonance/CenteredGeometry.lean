import CentralConfigurations.FiveBody.D2Resonance.PositiveClassification

namespace CentralConfigurations.FiveBody.D2.Resonance
set_option maxHeartbeats 2000000

noncomputable def resonanceWeight : ℝ := 2+2*Real.sqrt 2
noncomputable def resonanceShift : ℝ := Real.sqrt 2-1

theorem resonanceShift_pos : 0<resonanceShift := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp := Real.sqrt_nonneg 2
  dsimp [resonanceShift]
  nlinarith

theorem resonanceWeight_pos : 0<resonanceWeight := by
  dsimp [resonanceWeight]
  positivity

theorem resonanceWeight_sq : 18<resonanceWeight^2 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp := resonanceShift_pos
  dsimp [resonanceWeight,resonanceShift] at *
  nlinarith

theorem resonance_norm_factors {x : ℂ} (hr : 2*x.re=resonanceShift)
    (hn : Complex.normSq x=resonanceShift) :
    Complex.normSq ((resonanceWeight:ℂ)+x)=
      resonanceWeight^2+(resonanceWeight+1)*resonanceShift ∧
    Complex.normSq (2-x)=4-resonanceShift ∧
    Complex.normSq (((resonanceWeight+1:ℝ):ℂ)*x-(resonanceWeight:ℂ))=
      resonanceWeight^2+(resonanceWeight+1)*resonanceShift := by
  simp only [Complex.normSq_apply] at hn ⊢
  simp only [Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.re_ofNat,Complex.im_ofNat,zero_mul,add_zero,sub_zero]
  constructor
  · linear_combination hn+resonanceWeight*hr
  constructor
  · linear_combination hn-2*hr
  · linear_combination (resonanceWeight+1)^2*hn-
      resonanceWeight*(resonanceWeight+1)*hr

theorem resonance_norm_gap :
    4*(4-resonanceShift)<resonanceWeight^2+(resonanceWeight+1)*resonanceShift := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hp := resonanceShift_pos
  dsimp [resonanceWeight,resonanceShift] at *
  nlinarith

theorem centered_resonance_norms {x g : ℂ} {w : Fin 3 → ℂ}
    (hg : g≠0) (hr : 2*x.re=resonanceShift) (hn : Complex.normSq x=resonanceShift)
    (hd01 : w 1-w 0=g) (hd02 : w 2-w 0=g*x)
    (hc : w 0+(resonanceWeight:ℂ)*w 1+w 2=0) :
    ‖w 0‖^2=‖w 2‖^2 ∧ 4*‖w 1‖^2<‖w 0‖^2 := by
  have hp0 : ((resonanceWeight+2:ℝ):ℂ)*w 0=
      -g*((resonanceWeight:ℂ)+x) := by
    push_cast
    linear_combination hc-(resonanceWeight:ℂ)*hd01-hd02
  have hp1 : ((resonanceWeight+2:ℝ):ℂ)*w 1=g*(2-x) := by
    push_cast
    linear_combination hc+2*hd01-hd02
  have hp2 : ((resonanceWeight+2:ℝ):ℂ)*w 2=
      g*(((resonanceWeight+1:ℝ):ℂ)*x-(resonanceWeight:ℂ)) := by
    push_cast
    linear_combination hc-(resonanceWeight:ℂ)*hd01+
      ((resonanceWeight:ℂ)+1)*hd02
  obtain ⟨h0,h1,h2⟩ := resonance_norm_factors hr hn
  have he0 := congrArg Complex.normSq hp0
  have he1 := congrArg Complex.normSq hp1
  have he2 := congrArg Complex.normSq hp2
  simp only [Complex.normSq_mul,Complex.normSq_neg,Complex.normSq_ofReal] at he0 he1 he2
  rw [h0] at he0
  rw [h1] at he1
  rw [h2] at he2
  have hnK : 0<(resonanceWeight+2)^2 := by have := resonanceWeight_pos; positivity
  have hnG : 0<Complex.normSq g := Complex.normSq_pos.mpr hg
  have hout : Complex.normSq (w 0)=Complex.normSq (w 2) := by
    apply mul_left_cancel₀ (ne_of_gt hnK)
    linear_combination he0-he2
  have hheavy : 4*Complex.normSq (w 1)<Complex.normSq (w 0) := by
    have hgap := mul_pos hnG (sub_pos.mpr resonance_norm_gap)
    have hdiff : (resonanceWeight+2)^2*(Complex.normSq (w 0)-4*Complex.normSq (w 1))=
        Complex.normSq g*(resonanceWeight^2+(resonanceWeight+1)*resonanceShift-
          4*(4-resonanceShift)) := by linear_combination he0-4*he1
    have hp : 0<Complex.normSq (w 0)-4*Complex.normSq (w 1) :=
      (mul_pos_iff_of_pos_left hnK).mp (hdiff.symm ▸ hgap)
    linarith
  simpa only [Complex.sq_norm] using And.intro hout hheavy

end CentralConfigurations.FiveBody.D2.Resonance
