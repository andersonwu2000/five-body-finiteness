import CentralConfigurations.Asymptotics.PairEstimates

/-!
# Product bounds for the distance-order table

All roots are avoided: the inverse-distance witness already satisfies r^2=zw,
and asymptotic power cancellation acts on norms. These are the product
comparisons used in Lemma 4.2.
-/

namespace CentralConfigurations

open Filter Asymptotics

namespace PairEstimateData

variable (p : PairEstimateData)

theorem radius_littleO_scale_of_z (hz : p.z =o[atTop] p.scale) :
    p.radius =o[atTop] p.scale := by
  have hp : (fun t => p.radius t ^ 2) =o[atTop] (fun t => p.scale t ^ 2) :=
    (hz.mul_isBigO p.w_upper).congr
      (fun t => (p.radius_sq t).symm) (fun _ => by dsimp [scale]; ring)
  exact hp.of_pow (by decide : (2 : ℕ) ≠ 0)

theorem radius_littleO_scale_of_w (hw : p.w =o[atTop] p.scale) :
    p.radius =o[atTop] p.scale := p.swap.radius_littleO_scale_of_z hw

theorem radius_theta_scale_of_both (hz : p.z =Θ[atTop] p.scale)
    (hw : p.w =Θ[atTop] p.scale) : p.radius =Θ[atTop] p.scale := by
  apply theta_of_powers (k := 2) (by decide)
  exact theta_congr_pointwise (hz.mul hw)
    (fun t => (p.radius_sq t).symm) (fun _ => by ring)

theorem one_littleO_radius_of_z_large_w_maximal
    (hz : (fun t => p.eps t ^ 2) =o[atTop] p.z)
    (hw : p.w =Θ[atTop] p.scale) : (fun _ => (1 : ℂ)) =o[atTop] p.radius := by
  have hp : (fun _ => (1 : ℂ) ^ 2) =o[atTop] (fun t => p.radius t ^ 2) :=
    (hz.mul_isBigO hw.2).congr
      (fun t => by dsimp [scale]; field_simp [p.eps_ne_zero t])
      (fun t => (p.radius_sq t).symm)
  exact hp.of_pow (by decide : (2 : ℕ) ≠ 0)

end PairEstimateData

end CentralConfigurations
