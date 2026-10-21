import CentralConfigurations.FiveBody.D6Butterfly.WingOrders

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology

/-- Algebraic second-order inverse-cube expansion at a fixed nonzero complex
root. No differentiability or parameterization of the sequence is assumed. -/
theorem inverse_cube_second_order {f e t : ℕ → ℂ} {u s : ℂ}
    (_hu : u≠0) (hs : s≠0) (hu2 : u^2*s=1)
    (ht : Tendsto t atTop (𝓝 0))
    (he : e =O[atTop] (fun n => t n^2))
    (hf : (fun n => f n-u) =O[atTop] (fun n => t n^2))
    (hmetric : ∀ n, f n^2*(s+e n)=1) :
    (fun n => f n^3-u^3+(3/2:ℂ)*u^5*e n) =O[atTop] (fun n => t n^4) := by
  have ht2 : Tendsto (fun n => t n^2) atTop (𝓝 0) := by simpa using ht.pow 2
  have hvb := (hf.trans_tendsto ht2).isBigO_one ℂ
  have heb := (he.trans_tendsto ht2).isBigO_one ℂ
  have hvv : (fun n => (f n-u)^2) =O[atTop] (fun n => t n^4) := by
    simpa only [← pow_mul] using hf.pow 2
  have hve : (fun n => (f n-u)*e n) =O[atTop] (fun n => t n^4) := by
    simpa only [← pow_add] using hf.mul he
  have h := (((((hvv.const_mul_left s).add (hve.const_mul_left (2*u))).add
      (order_mul_bounded hvv heb)).const_mul_left (-(3*u)/(2*s))).add
      (hvv.const_mul_left (3*u))).add (order_mul_bounded hvv hvb)
  apply h.congr_left
  intro n
  have hh := hmetric n
  field_simp [hs]
  linear_combination -3*u*hh+(3*u-3*u^3*e n)*hu2

end CentralConfigurations.FiveBody.D6
