import CentralConfigurations.Asymptotics.ClusterPairLimits

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

/-- A nonzero limiting denominator gives a bounded division operator along
the actual sequence; finite initial zeros do not matter. -/
theorem divide_bigO {f d a : ℕ → ℂ} {v : ℂ}
    (hf : f =O[atTop] a) (hd : Tendsto d atTop (𝓝 v)) (hv : v≠0) :
    (fun t => f t/d t) =O[atTop] a := by
  have hi := (hd.inv₀ hv).isBigO_one ℂ
  simpa only [div_eq_mul_inv,mul_one] using hf.mul hi

theorem square_root_difference_bigO {f a : ℕ → ℂ} {u : ℂ}
    (hu : u≠0) (hlim : Tendsto f atTop (𝓝 u))
    (h : (fun t => f t^2-u^2) =O[atTop] a) :
    (fun t => f t-u) =O[atTop] a := by
  have hd := hlim.add_const u
  have hn : u+u≠0 := by intro hh; apply hu; linear_combination (1/2:ℂ)*hh
  have ho := divide_bigO h hd hn
  apply ho.congr'
  · filter_upwards [hd.eventually_ne hn] with t ht
    apply (div_eq_iff ht).2
    ring
  · exact Eventually.of_forall (fun _ => rfl)

theorem cube_root_difference_bigO {f a : ℕ → ℂ} {u : ℂ}
    (hu : u≠0) (hlim : Tendsto f atTop (𝓝 u))
    (h : (fun t => f t^3-u^3) =O[atTop] a) :
    (fun t => f t-u) =O[atTop] a := by
  have hd := ((hlim.pow 2).add (hlim.mul_const u)).add_const (u^2)
  have hn : u^2+u*u+u^2≠0 := by
    rw [show u^2+u*u+u^2=3*u^2 by ring]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hu)
  have ho := divide_bigO h hd hn
  apply ho.congr'
  · filter_upwards [hd.eventually_ne hn] with t ht
    apply (div_eq_iff ht).2
    ring
  · exact Eventually.of_forall (fun _ => rfl)

theorem inverse_difference_bigO {f a : ℕ → ℂ} {u : ℂ}
    (hu : u≠0) (hlim : Tendsto f atTop (𝓝 u))
    (h : (fun t => f t-u) =O[atTop] a) :
    (fun t => (f t)⁻¹-u⁻¹) =O[atTop] a := by
  have hd := hlim.mul_const u
  have ho := divide_bigO h.neg_left hd (mul_ne_zero hu hu)
  apply ho.congr'
  · filter_upwards [hlim.eventually_ne hu] with t ht
    field_simp [ht,hu]
    ring
  · exact Eventually.of_forall (fun _ => rfl)

/-- Every extracted branch has its correction rate forced by the exact
metric equation, without an assumed Puiseux expansion. -/
theorem inverse_square_metric_rigidity {f e a : ℕ → ℂ} {u s : ℂ}
    (hu : u≠0) (hs : s≠0) (hlim : Tendsto f atTop (𝓝 u))
    (hroot : u^2*s=1) (hmetric : ∀ t, f t^2*(s+e t)=1)
    (he : e =O[atTop] a) : (fun t => f t-u) =O[atTop] a := by
  apply square_root_difference_bigO hu hlim
  have hb := (hlim.pow 2).isBigO_one ℂ
  have h := (he.mul hb).const_mul_left (-s⁻¹)
  simpa only [mul_one] using h.congr_left (fun t => by
    field_simp [hs]
    linear_combination -(hmetric t)+hroot)

theorem pair_square_root_difference_bigO {f g a : ℕ → ℂ} {u : ℂ}
    (hu : u≠0) (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 u))
    (h : (fun t => f t^2-g t^2) =O[atTop] a) : (fun t => f t-g t) =O[atTop] a := by
  have hd := hf.add hg
  have hn : u+u≠0 := by intro hh; apply hu; linear_combination (1/2:ℂ)*hh
  apply (divide_bigO h hd hn).congr'
  · filter_upwards [hd.eventually_ne hn] with t ht
    apply (div_eq_iff ht).2
    ring
  · exact Eventually.of_forall (fun _ => rfl)

theorem pair_cube_root_difference_bigO {f g a : ℕ → ℂ} {u : ℂ}
    (hu : u≠0) (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 u))
    (h : (fun t => f t^3-g t^3) =O[atTop] a) : (fun t => f t-g t) =O[atTop] a := by
  have hd := ((hf.pow 2).add (hf.mul hg)).add (hg.pow 2)
  have hn : u^2+u*u+u^2≠0 := by
    rw [show u^2+u*u+u^2=3*u^2 by ring]
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hu)
  apply (divide_bigO h hd hn).congr'
  · filter_upwards [hd.eventually_ne hn] with t ht
    apply (div_eq_iff ht).2
    ring
  · exact Eventually.of_forall (fun _ => rfl)

theorem pair_inverse_difference_bigO {f g a : ℕ → ℂ} {u v : ℂ}
    (hu : u≠0) (hv : v≠0) (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v))
    (h : (fun t => f t-g t) =O[atTop] a) : (fun t => (f t)⁻¹-(g t)⁻¹) =O[atTop] a := by
  apply (divide_bigO h.neg_left (hf.mul hg) (mul_ne_zero hu hv)).congr'
  · filter_upwards [hf.eventually_ne hu,hg.eventually_ne hv] with t ht ht'
    field_simp [ht,ht']
    ring
  · exact Eventually.of_forall (fun _ => rfl)

theorem pair_inverse_square_difference_bigO {f g a : ℕ → ℂ} {u v : ℂ}
    (hu : u≠0) (hv : v≠0) (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v))
    (h : (fun t => f t-g t) =O[atTop] a) : (fun t => (f t)⁻¹^2-(g t)⁻¹^2) =O[atTop] a := by
  have hdiff := pair_inverse_difference_bigO hu hv hf hg h
  have hsum := ((hf.inv₀ hu).add (hg.inv₀ hv)).isBigO_one ℂ
  simpa only [mul_one] using (hdiff.mul hsum).congr_left (fun t => by ring)

theorem cube_difference_bigO {f g a : ℕ → ℂ} {u v : ℂ}
    (hf : Tendsto f atTop (𝓝 u)) (hg : Tendsto g atTop (𝓝 v))
    (h : (fun t => f t-g t) =O[atTop] a) : (fun t => f t^3-g t^3) =O[atTop] a := by
  have hp := (((hf.pow 2).add (hf.mul hg)).add (hg.pow 2)).isBigO_one ℂ
  simpa only [mul_one] using (h.mul hp).congr_left (fun t => by ring)

end CentralConfigurations.FiveBody.D6
