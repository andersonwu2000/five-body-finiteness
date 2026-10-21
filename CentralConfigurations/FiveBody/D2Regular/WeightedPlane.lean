import CentralConfigurations.FiveBody.D2Regular.Gauge

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 3000000

def weightedCenter (n v : Fin 3 → ℂ) : ℂ := ∑ i, n i*v i
def bilinear (n v w : Fin 3 → ℂ) : ℂ := ∑ i, n i*v i*w i
def transverse (n d : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![(d 1-d 2)/n 0,(d 2-d 0)/n 1,(d 0-d 1)/n 2]

theorem transverse_centered (n d : Fin 3 → ℂ) (hn : ∀ i, n i≠0) :
    weightedCenter n (transverse n d)=0 := by
  simp [weightedCenter,transverse,Fin.sum_univ_succ]
  field_simp [hn 0,hn 1,hn 2]
  ring

theorem transverse_orthogonal (n d : Fin 3 → ℂ) (hn : ∀ i, n i≠0) :
    bilinear n d (transverse n d)=0 := by
  simp [bilinear,transverse,Fin.sum_univ_succ]
  field_simp [hn 0,hn 1,hn 2]
  ring

theorem transverse_span (n d v : Fin 3 → ℂ) (hn : ∀ i, n i≠0)
    (hd : d 0-d 1≠0) (hv : weightedCenter n v=0) (hp : bilinear n d v=0) :
    ∀ i, v i=(n 2*v 2/(d 0-d 1))*transverse n d i := by
  simp [weightedCenter,bilinear,Fin.sum_univ_succ] at hv hp
  intro i
  fin_cases i <;> dsimp [transverse]
  all_goals field_simp [hd,hn 0,hn 1,hn 2]
  · linear_combination hp-d 1*hv
  · linear_combination d 0*hv-hp

theorem transverse_norm (n d : Fin 3 → ℂ) (hn : ∀ i, n i≠0)
    (hd : weightedCenter n d=0) :
    bilinear n (transverse n d) (transverse n d)=
      (n 0+n 1+n 2)*bilinear n d d/(n 0*n 1*n 2) := by
  simp [weightedCenter,Fin.sum_univ_succ] at hd
  simp [bilinear,transverse,Fin.sum_univ_succ]
  field_simp [hn 0,hn 1,hn 2]
  linear_combination -(n 0*d 0+n 1*d 1+n 2*d 2)*hd

theorem transverse_no_isotropic (n d v : Fin 3 → ℂ) (hn : ∀ i, n i≠0)
    (hB : n 0+n 1+n 2≠0) (hd : d 0-d 1≠0)
    (hc : weightedCenter n d=0) (hS : bilinear n d d≠0)
    (hv : weightedCenter n v=0) (hp : bilinear n d v=0)
    (hvv : bilinear n v v=0) : ∀ i, v i=0 := by
  have he := transverse_span n d v hn hd hv hp
  let t := n 2*v 2/(d 0-d 1)
  have he' : v=fun i => t*transverse n d i := funext he
  have hh : t^2*bilinear n (transverse n d) (transverse n d)=0 := by
    rw [he'] at hvv
    dsimp [bilinear] at hvv ⊢
    calc
      _=(∑ i, n i*(t*transverse n d i)*(t*transverse n d i)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _=0 := hvv
  have hen : bilinear n (transverse n d) (transverse n d)≠0 := by
    rw [transverse_norm n d hn hc]
    exact div_ne_zero (mul_ne_zero hB hS) (mul_ne_zero (mul_ne_zero (hn 0) (hn 1)) (hn 2))
  have ht : t=0 := by
    have hh' := (mul_eq_zero.mp hh).resolve_right hen
    exact (pow_eq_zero_iff (by decide : 2≠0)).mp hh'
  intro i
  rw [he i]
  change t*transverse n d i=0
  rw [ht,zero_mul]

def laplacian (n : Fin 3 → ℂ) (delta : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (i : Fin 3) : ℂ :=
  ∑ j, n j*delta i j^3*(v i-v j)

theorem laplacian_transverse_identity (n d : Fin 3 → ℂ) (delta : Fin 3 → Fin 3 → ℂ)
    (hn : ∀ i, n i≠0) (hs : ∀ i j, delta i j=delta j i) (i : Fin 3) :
    laplacian n delta (transverse n d) i=
      ((n 0+n 1)*delta 0 1^3+(n 0+n 2)*delta 0 2^3+(n 1+n 2)*delta 1 2^3)*
        transverse n d i-transverse n (laplacian n delta d) i := by
  fin_cases i <;>
    simp [laplacian,transverse,Fin.sum_univ_succ,hs 1 0,hs 2 0,hs 2 1]
  all_goals field_simp [hn 0,hn 1,hn 2]
  all_goals ring

theorem actual_transverse_eigenvector {n : Fin 3 → ℂ} (r : ZWSystem ℂ 3 n)
    (hn : ∀ i, n i≠0) (i : Fin 3) :
    laplacian n r.delta (transverse n r.w) i=transverseEigenvalue r*transverse n r.w i := by
  have hh : laplacian n r.delta r.w=r.w := by
    funext j
    exact (r.force_w j).symm
  rw [laplacian_transverse_identity n r.w r.delta hn r.delta_symm i,hh]
  dsimp [transverseEigenvalue]
  ring

end
end CentralConfigurations.FiveBody.D2.Regular
