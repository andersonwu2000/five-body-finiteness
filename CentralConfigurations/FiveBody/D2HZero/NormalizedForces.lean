import CentralConfigurations.FiveBody.D2HZero.CircleChart
import CentralConfigurations.FiveBody.D2Exceptional.HZeroQuintic

namespace CentralConfigurations.FiveBody.D2.HZero
open scoped BigOperators
set_option maxHeartbeats 4000000

theorem normalize_force_rows {a b c γ θ σ01 σ02 σ12 ω y : ℂ}
    (hγ : γ ≠ 0) (hω : ω ≠ 1) (hy : y ≠ 1) (hyω : y ≠ ω) (hσ : σ01^2=1)
    (h0 : θ^3*γ=b*σ01/(γ-γ*ω)^2+c*σ02/(γ-γ*y)^2)
    (h1 : θ^3*(γ*ω)= -a*σ01/(γ*ω-γ)^2+c*σ12/(γ*ω-γ*y)^2) :
    -σ01*θ^3*γ^3= -b/(ω-1)^2-c*(σ01*σ02)/(y-1)^2 ∧
    (-σ01*θ^3*γ^3)*ω=a/(ω-1)^2-c*(σ01*σ12)/(y-ω)^2 := by
  have hd01 : γ-γ*ω = -γ*(ω-1) := by ring
  have hd02 : γ-γ*y = -γ*(y-1) := by ring
  have hd10 : γ*ω-γ = γ*(ω-1) := by ring
  have hd12 : γ*ω-γ*y = -γ*(y-ω) := by ring
  rw [hd01,hd02] at h0
  rw [hd10,hd12] at h1
  have h0n : θ^3*γ^3=b*σ01/(ω-1)^2+c*σ02/(y-1)^2 := by
    field_simp [hγ,sub_ne_zero.mpr hω,sub_ne_zero.mpr hy] at h0 ⊢
    linear_combination h0
  have h1n : θ^3*γ^3*ω= -a*σ01/(ω-1)^2+c*σ12/(y-ω)^2 := by
    field_simp [hγ,sub_ne_zero.mpr hω,sub_ne_zero.mpr hyω] at h1 ⊢
    linear_combination h1
  constructor
  · rw [show -σ01*θ^3*γ^3= -σ01*(θ^3*γ^3) by ring,h0n]
    field_simp [sub_ne_zero.mpr hω,sub_ne_zero.mpr hy]
    linear_combination -b*(y-1)^2*hσ
  · rw [show (-σ01*θ^3*γ^3)*ω= -σ01*(θ^3*γ^3*ω) by ring,h1n]
    field_simp [sub_ne_zero.mpr hω,sub_ne_zero.mpr hyω]
    linear_combination a*(y-ω)^2*hσ

theorem CircleChart.positions {m : Fin 5 → ℝ} {s : FiveBodySource18Certificate m}
    (c : CircleChart s) (i : Fin 3) :
    s.triangle.w (c.order i)=c.gamma*(![1,c.omega,c.y] i) := by
  fin_cases i
  · simp [CircleChart.gamma]
  · simpa [mul_comm,CircleChart.omega] using (div_eq_iff c.gamma_ne_zero).mp c.pair_ratio
  · dsimp [CircleChart.y]
    rw [mul_div_cancel₀ _ c.gamma_ne_zero]

def CircleChart.mass {m : Fin 5 → ℝ} {s : FiveBodySource18Certificate m}
    (c : CircleChart s) (i : Fin 3) : ℝ := m ((c.order i).castLE (by decide))

structure OriginalRows {m : Fin 5 → ℝ} {s : FiveBodySource18Certificate m}
    (c : CircleChart s) (signed : SignedEulerMetric s.triangle) where
  lam : ℂ
  lam_eq : lam= -signed.sign (c.order 0) (c.order 1)*signed.theta^3*c.gamma^3
  sign13 : ℂ
  sign23 : ℂ
  sign13_eq : sign13=signed.sign (c.order 0) (c.order 1)*signed.sign (c.order 0) (c.order 2)
  sign23_eq : sign23=signed.sign (c.order 0) (c.order 1)*signed.sign (c.order 1) (c.order 2)
  sign13_values : sign13=1 ∨ sign13=-1
  sign23_values : sign23=1 ∨ sign23=-1
  center : (c.mass 0 : ℂ)+(c.mass 1 : ℂ)*c.omega+(c.mass 2 : ℂ)*c.y=0
  row0 : lam= -(c.mass 1 : ℂ)/(c.omega-1)^2-(c.mass 2 : ℂ)*sign13/(c.y-1)^2
  row1 : lam*c.omega=(c.mass 0 : ℂ)/(c.omega-1)^2-(c.mass 2 : ℂ)*sign23/(c.y-c.omega)^2

theorem exists_originalRows {m : Fin 5 → ℝ} {s : FiveBodySource18Certificate m}
    (c : CircleChart s) (signed : SignedEulerMetric s.triangle) : Nonempty (OriginalRows c signed) := by
  let e := c.order
  have hneq (i j : Fin 3) (hij : i ≠ j) : e i ≠ e j := e.injective.ne hij
  have hsign01 := signed.sign_values (e 0) (e 1) (hneq 0 1 (by decide))
  have hsign02 := signed.sign_values (e 0) (e 2) (hneq 0 2 (by decide))
  have hsign12 := signed.sign_values (e 1) (e 2) (hneq 1 2 (by decide))
  have hsquare : signed.sign (e 0) (e 1)^2=1 := by
    rcases hsign01 with h | h <;> rw [h] <;> norm_num
  have hs13 : signed.sign (e 0) (e 1)*signed.sign (e 0) (e 2)=1 ∨
      signed.sign (e 0) (e 1)*signed.sign (e 0) (e 2)=-1 := by
    rcases hsign01 with h | h <;> rcases hsign02 with h' | h' <;> rw [h,h'] <;> norm_num
  have hs23 : signed.sign (e 0) (e 1)*signed.sign (e 1) (e 2)=1 ∨
      signed.sign (e 0) (e 1)*signed.sign (e 1) (e 2)=-1 := by
    rcases hsign01 with h | h <;> rcases hsign12 with h' | h' <;> rw [h,h'] <;> norm_num
  have h0 := signed.euler_force (e 0)
  have h1 := signed.euler_force (e 1)
  rw [← Equiv.sum_comp e (fun j => (m (j.castLE (by decide)) : ℂ)*signed.sign (e 0) j/
    (s.triangle.w (e 0)-s.triangle.w j)^2)] at h0
  rw [← Equiv.sum_comp e (fun j => (m (j.castLE (by decide)) : ℂ)*signed.sign (e 1) j/
    (s.triangle.w (e 1)-s.triangle.w j)^2)] at h1
  simp [Fin.sum_univ_succ,signed.sign_diagonal] at h0 h1
  rw [signed.sign_antisymm (e 0) (e 1)] at h1
  change _ = (c.mass 1 : ℂ)*signed.sign (e 0) (e 1)/_+
    (c.mass 2 : ℂ)*signed.sign (e 0) (e 2)/_ at h0
  change _ = (c.mass 0 : ℂ)*(-signed.sign (e 0) (e 1))/_+
    (c.mass 2 : ℂ)*signed.sign (e 1) (e 2)/_ at h1
  dsimp [e] at h0 h1 hsquare hs13 hs23
  rw [c.positions 0,c.positions 1,c.positions 2] at h0 h1
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,mul_one] at h0 h1
  obtain ⟨hr0,hr1⟩ := normalize_force_rows c.gamma_ne_zero c.omega_ne_one c.y_ne_one c.y_ne_omega
    hsquare h0 (by simpa only [mul_neg,neg_mul] using h1)
  have hc := (Equiv.sum_comp c.order (fun j =>
    (m (j.castLE (by decide)) : ℂ)*s.triangle.w j)).trans s.triangle.mass_center_w
  simp [Fin.sum_univ_succ] at hc
  rw [c.positions 0,c.positions 1,c.positions 2] at hc
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,mul_one] at hc
  change (c.mass 0 : ℂ)*c.gamma+((c.mass 1 : ℂ)*(c.gamma*c.omega)+
    (c.mass 2 : ℂ)*(c.gamma*c.y))=0 at hc
  have hcenter : (c.mass 0 : ℂ)+(c.mass 1 : ℂ)*c.omega+(c.mass 2 : ℂ)*c.y=0 := by
    apply mul_left_cancel₀ c.gamma_ne_zero
    linear_combination hc
  exact ⟨⟨_,rfl,_,_,rfl,rfl,hs13,hs23,hcenter,hr0,hr1⟩⟩

end CentralConfigurations.FiveBody.D2.HZero
