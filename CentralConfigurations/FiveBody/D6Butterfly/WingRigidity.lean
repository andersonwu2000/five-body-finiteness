import CentralConfigurations.FiveBody.D6Butterfly.RootOrders

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

/-- The source's scalar wing-closure argument. The three residuals are
proved from actual force and distance equations in `wing_residuals`. This lemma does not invert
a full Jacobian, choose a real sheet, or assume a correction rate. -/
theorem wing_rigidity {r f g ε : ℕ → ℂ} {R F G A C : ℂ}
    (hR : R≠0) (hF : F≠0) (hG : G≠0)
    (hr : Tendsto r atTop (𝓝 R)) (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 G))
    (hε : Tendsto ε atTop (𝓝 0))
    (hfg : (fun t => f t^3-g t^3) =O[atTop] ε)
    (hnorm : (fun t => A*r t^3+C*f t^3-1) =O[atTop] ε)
    (hclosure : (fun t => (r t)⁻¹^2-2*(f t)⁻¹^2-2*(g t)⁻¹^2) =O[atTop] ε) :
    (fun t => r t^3-R^3) =O[atTop] ε ∧
    (fun t => f t^3-F^3) =O[atTop] ε ∧
    (fun t => g t^3-G^3) =O[atTop] ε := by
  have hFG : F^3=G^3 := sub_eq_zero.mp (tendsto_nhds_unique
    ((hf.pow 3).sub (hg.pow 3)) (hfg.trans_tendsto hε))
  have hN : A*R^3+C*F^3=1 := sub_eq_zero.mp (tendsto_nhds_unique
    (((hr.pow 3).const_mul A).add ((hf.pow 3).const_mul C) |>.sub_const 1)
    (hnorm.trans_tendsto hε))
  have hL : R⁻¹^2-2*F⁻¹^2-2*G⁻¹^2=0 := tendsto_nhds_unique
    ((((hr.inv₀ hR).pow 2).sub (((hf.inv₀ hF).pow 2).const_mul 2)).sub
      (((hg.inv₀ hG).pow 2).const_mul 2)) (hclosure.trans_tendsto hε)
  let ρ := G/F
  let σ := R/F
  have hρF : ρ*F=G := div_mul_cancel₀ _ hF
  have hσF : σ*F=R := div_mul_cancel₀ _ hF
  have hρ : ρ≠0 := div_ne_zero hG hF
  have hσ : σ≠0 := div_ne_zero hR hF
  have hρ3 : ρ^3=1 := by dsimp [ρ]; rw [div_pow,← hFG]; exact div_self (pow_ne_zero 3 hF)
  have hC : 2+2*ρ⁻¹^2=σ⁻¹^2 := by
    dsimp [ρ,σ]
    field_simp [hR,hF,hG] at hL ⊢
    linear_combination -hL
  have hρf : Tendsto (fun t => ρ*f t) atTop (𝓝 G) := by simpa only [hρF] using hf.const_mul ρ
  have hσf : Tendsto (fun t => σ*f t) atTop (𝓝 R) := by simpa only [hσF] using hf.const_mul σ
  have hcg : (fun t => g t^3-(ρ*f t)^3) =O[atTop] ε :=
    hfg.neg_left.congr_left (fun t => by rw [mul_pow,hρ3]; ring)
  have hsg := pair_cube_root_difference_bigO hG hg hρf hcg
  have hig := pair_inverse_square_difference_bigO hG hG hg hρf hsg
  have hcl : (fun t => (r t)⁻¹^2-σ⁻¹^2*(f t)⁻¹^2) =O[atTop] ε := by
    apply (hclosure.add (hig.const_mul_left 2)).congr_left
    intro t
    simp only [mul_inv,mul_pow]
    rw [← hC]
    ring
  have hb := ((hr.pow 2).mul (hf.pow 2)).isBigO_one ℂ
  have hsq : (fun t => r t^2-(σ*f t)^2) =O[atTop] ε := by
    have h := ((hcl.mul hb).const_mul_left (-σ^2))
    have hh : (fun t => -σ^2*((r t)⁻¹^2-σ⁻¹^2*(f t)⁻¹^2)*(r t^2*f t^2)) =O[atTop] ε := by
      simpa only [mul_one,mul_assoc] using h
    apply hh.congr'
    · filter_upwards [hr.eventually_ne hR,hf.eventually_ne hF] with t hrt hft
      field_simp [hrt,hft,hσ]
      ring
    · exact Eventually.of_forall (fun _ => rfl)
  have hsr := pair_square_root_difference_bigO hR hr hσf hsq
  have hcr := cube_difference_bigO hr hσf hsr
  let K := A*σ^3+C
  have hK : K*F^3=1 := by
    dsimp [K]
    calc
      _ = A*(σ*F)^3+C*F^3 := by ring
      _ = 1 := by rw [hσF]; exact hN
  have hKn : K≠0 := by intro h; rw [h,zero_mul] at hK; norm_num at hK
  have hsmallf : (fun t => f t^3-F^3) =O[atTop] ε := by
    apply ((hnorm.sub (hcr.const_mul_left A)).const_mul_left K⁻¹).congr_left
    intro t
    dsimp only
    apply (mul_left_cancel₀ hKn)
    field_simp [hKn]
    dsimp [K] at hK ⊢
    linear_combination hK
  have hsmallr : (fun t => r t^3-R^3) =O[atTop] ε := by
    apply (hcr.add (hsmallf.const_mul_left (σ^3))).congr_left
    intro t
    rw [← hσF]
    ring
  have hsmallg : (fun t => g t^3-G^3) =O[atTop] ε := by
    apply (hfg.neg_left.add hsmallf).congr_left
    intro t
    rw [hFG]
    ring
  exact ⟨hsmallr,hsmallf,hsmallg⟩

end CentralConfigurations.FiveBody.D6
