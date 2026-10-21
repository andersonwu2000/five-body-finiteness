import CentralConfigurations.FiveBody.D2Regular.BaseResidual

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000

theorem centered_torque_slope (n d e B : Fin 3 → ℂ) (hd : ∀ i, d i≠0)
    (he : weightedCenter n e=0) (hB : weightedCenter n B=0) :
    (∑ i, n i*B i*(e i-e 2*d i)/d i)=
      bilinear n e (centeredVector n (fun i => B i/d i)) := by
  let K := weightedCenter n (fun i => B i/d i)/(n 0+n 1+n 2)
  have hh (i : Fin 3) : n i*B i*(e i-e 2*d i)/d i=
      n i*e i*centeredVector n (fun j => B j/d j) i+K*(n i*e i)-e 2*(n i*B i) := by
    dsimp [centeredVector]
    change n i*B i*(e i-e 2*d i)/d i=n i*e i*(B i/d i-K)+K*(n i*e i)-e 2*(n i*B i)
    field_simp [hd i]
    ring
  simp_rw [hh]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
  change bilinear n e (centeredVector n (fun i => B i/d i))+K*weightedCenter n e-e 2*weightedCenter n B=_
  rw [he,hB,mul_zero,mul_zero,add_zero,sub_zero]

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i:ℂ))}
  {l : ScaledZWLimit q (fun t => (q t).inverseScale)} {I0 : ℝ}
  (s : PhysicalEulerLimit m q l I0) (e : GaugeExtraction s.toActualLimit) (hm : ∀ i, 0<m i)

def leadingB (i : Fin 3) : ℂ := (m 3:ℂ)*(s.cross 0 i/e.ratio)+m 4*(s.cross 1 i/e.ratio)
def leadingH : Fin 3 → ℂ := centeredVector (shapeMass m) (fun i => leadingB s e i/leadingD s i)
def torqueResponse : ℂ := bilinear (shapeMass m) (leadingE s) (leadingH s e)

theorem leadingD_ne (i : Fin 3) : leadingD s i≠0 := by
  simpa [leadingD,normalizedTriangle,ZWSystem.rescale,div_eq_mul_inv,mul_comm] using div_ne_zero (s.w_ne_zero i) (s.w_ne_zero 2)

theorem leadingB_centered : weightedCenter (shapeMass m) (leadingB s e)=0 := by
  have hh := s.cross_torque
  dsimp [weightedCenter,leadingB,shapeMass]
  simp [Fin.sum_univ_succ,tripleIndex] at hh ⊢
  field_simp [e.ratio_ne]
  linear_combination hh

theorem leadingH_transport (i : Fin 3) :
    leadingH s e i=(s.triangle.w 2/e.ratio)*HZero.centeredCrossResponse s.toFiveBodySource18Certificate i := by
  simpa [leadingH,leadingB,leadingD,normalizedTriangle,ZWSystem.rescale,div_eq_mul_inv,mul_comm] using response_gauge_transport s.toFiveBodySource18Certificate e.ratio_ne (s.w_ne_zero 2) i

include hm in
theorem leadingH_centered : weightedCenter (shapeMass m) (leadingH s e)=0 := by
  apply centeredVector_center
  change (m 0:ℂ)+m 1+m 2≠0
  exact_mod_cast ne_of_gt (add_pos (add_pos (hm 0) (hm 1)) (hm 2))

theorem leadingH_orthogonal : bilinear (shapeMass m) (leadingD s) (leadingH s e)=0 :=
  centeredVector_orthogonal (shapeMass m) (leadingD s) (leadingB s e) (leadingD_ne s)
    (normalizedTriangle s).mass_center_w (leadingB_centered s e)

include hm in
theorem leadingH_norm_ne : bilinear (shapeMass m) (leadingH s e) (leadingH s e)≠0 := by
  have hh : bilinear (shapeMass m) (leadingH s e) (leadingH s e)=
      (s.triangle.w 2/e.ratio)^2*bilinear (shapeMass m)
        (HZero.centeredCrossResponse s.toFiveBodySource18Certificate)
        (HZero.centeredCrossResponse s.toFiveBodySource18Certificate) := by
    dsimp [bilinear]
    simp_rw [leadingH_transport]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hh]
  exact mul_ne_zero (pow_ne_zero 2 (div_ne_zero (s.w_ne_zero 2) e.ratio_ne))
    (original_response_norm_ne s hm)

include hm in
theorem torqueResponse_ne : torqueResponse s e≠0 := by
  intro hT
  have hv := transverse_span (shapeMass m) (leadingD s) (leadingH s e)
    (fun i => Complex.ofReal_ne_zero.mpr (ne_of_gt (hm (tripleIndex i))))
    ((normalizedTriangle s).w_separation_ne_zero (by decide))
    (leadingH_centered s e hm) (leadingH_orthogonal s e)
  apply leadingH_norm_ne s e hm
  calc
    bilinear (shapeMass m) (leadingH s e) (leadingH s e)=
        (shapeMass m 2*leadingH s e 2/(leadingD s 0-leadingD s 1))*torqueResponse s e := by
      dsimp [bilinear,torqueResponse]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [hv i]
      dsimp [leadingE]
      ring
    _=0 := by rw [hT,mul_zero]

include hm in
theorem torque_slope_eq :
    (∑ i, shapeMass m i*leadingB s e i*(leadingE s i-leadingE s 2*leadingD s i)/leadingD s i)=
      torqueResponse s e := by
  exact centered_torque_slope (shapeMass m) (leadingD s) (leadingE s) (leadingB s e)
    (leadingD_ne s) (transverse_centered (shapeMass m) (leadingD s)
      (fun i => Complex.ofReal_ne_zero.mpr (ne_of_gt (hm (tripleIndex i))))) (leadingB_centered s e)

end
end CentralConfigurations.FiveBody.D2.Regular


