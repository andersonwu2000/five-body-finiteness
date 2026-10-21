import CentralConfigurations.FiveBody.D6Butterfly.StaticLimits

namespace CentralConfigurations.FiveBody.D6

theorem wing_sum_and_internal {a c R F G q0 q1 q2 : ℂ}
    (hR : R≠0) (hFG : F^3=G^3) (hN : 2*a*R^3+c*F^3=1)
    (h1 : q1=a*R^3*(q1-q2)+c*F^3*(q1-q0))
    (h2 : q2=a*R^3*(q2-q1)+c*G^3*(q2-q0)) :
    a*(q1+q2)= -c*(F^3/R^3)*q0 ∧
    a*F^3*(q0-q1)+a*G^3*(q0-q2)=(F^3/R^3)*q0 := by
  rw [← hFG] at h2 ⊢
  have hsum : a*(q1+q2)*R^3= -c*F^3*q0 := by
    linear_combination (h1+h2+(q1+q2)*hN)/2
  constructor
  · field_simp [hR]
    simpa only [neg_mul] using hsum
  · field_simp [hR]
    linear_combination F^3*q0*hN-F^3*hsum

noncomputable def reciprocalZ (u : Fin 6 → ℂ) : ℂ := u 3^3/u 5^3
noncomputable def reciprocalW (u : Fin 6 → ℂ) : ℂ := u 1^3/u 0^3

theorem WingStatic.reciprocal_data {a b d : ℂ} {c : Fin 8 → ℂ} {u : Fin 6 → ℂ}
    (hs : WingStatic a b d c u) (hun : ∀ e, u e≠0) :
    (reciprocalZ u^2=64 ∨ reciprocalZ u^2= -8) ∧
    (reciprocalW u^2=64 ∨ reciprocalW u^2= -8) ∧
    a*(c 6+c 7)= -d*reciprocalZ u*c 5 ∧
    b*(c 2+c 3)= -d*reciprocalW u*c 4 ∧
    a*u 3^3*(c 5-c 6)+a*u 4^3*(c 5-c 7)=reciprocalZ u*c 5 ∧
    b*u 1^3*(c 4-c 2)+b*u 2^3*(c 4-c 3)=reciprocalW u*c 4 := by
  obtain ⟨hq,hA⟩ := wing_sum_and_internal (hun 5) hs.z_equal hs.z_normal hs.q1 hs.q2
  obtain ⟨hp,hB⟩ := wing_sum_and_internal (hun 0) hs.w_equal hs.w_normal hs.p3 hs.p4
  exact ⟨wing_reciprocal_catalogue (hun 5) (hun 3) (hun 4) hs.z_equal hs.z_closure,
    wing_reciprocal_catalogue (hun 0) (hun 1) (hun 2) hs.w_equal hs.w_closure,hq,hp,hA,hB⟩

end CentralConfigurations.FiveBody.D6

