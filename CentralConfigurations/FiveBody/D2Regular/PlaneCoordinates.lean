import CentralConfigurations.FiveBody.D2Regular.WeightedPlane

namespace CentralConfigurations.FiveBody.D2.Regular
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 2000000

def parallelCoefficient (n d v : Fin 3 → ℂ) : ℂ := bilinear n d v/bilinear n d d
def transverseCoefficient (n d v : Fin 3 → ℂ) : ℂ :=
  n 2*(v 2-parallelCoefficient n d v*d 2)/(d 0-d 1)

theorem plane_decomposition (n d v : Fin 3 → ℂ) (hn : ∀ i, n i≠0)
    (hd : d 0-d 1≠0) (hS : bilinear n d d≠0)
    (hc : weightedCenter n d=0) (hv : weightedCenter n v=0) (i : Fin 3) :
    v i=parallelCoefficient n d v*d i+transverseCoefficient n d v*transverse n d i := by
  let rho := parallelCoefficient n d v
  let u : Fin 3 → ℂ := fun j => v j-rho*d j
  have hu : weightedCenter n u=0 := by
    simp [weightedCenter,Fin.sum_univ_succ] at hc hv ⊢
    dsimp [u]
    linear_combination hv-rho*hc
  have hp : bilinear n d u=0 := by
    have he : bilinear n d u=bilinear n d v-rho*bilinear n d d := by
      simp [bilinear,Fin.sum_univ_succ,u]
      ring
    rw [he]
    dsimp [rho,parallelCoefficient]
    field_simp [hS]
    ring
  have he := transverse_span n d u hn hd hu hp i
  change v i-rho*d i=transverseCoefficient n d v*transverse n d i at he
  linear_combination he

theorem gauge_plane_decomposition (n d v : Fin 3 → ℂ) (hn : ∀ i, n i≠0)
    (hd : d 0-d 1≠0) (hS : bilinear n d d≠0)
    (hc : weightedCenter n d=0) (hv : weightedCenter n v=0)
    (hd2 : d 2=1) (hv2 : v 2=1) (i : Fin 3) :
    v i=d i+transverseCoefficient n d v*(transverse n d i-transverse n d 2*d i) := by
  have he := plane_decomposition n d v hn hd hS hc hv i
  have h2 := plane_decomposition n d v hn hd hS hc hv 2
  rw [hd2,hv2,mul_one] at h2
  linear_combination he-d i*h2

theorem parallel_self (n d : Fin 3 → ℂ) (hS : bilinear n d d≠0) :
    parallelCoefficient n d d=1 := by simp [parallelCoefficient,hS]

theorem transverse_self (n d : Fin 3 → ℂ) (hS : bilinear n d d≠0) :
    transverseCoefficient n d d=0 := by simp [transverseCoefficient,parallel_self n d hS]

theorem parallel_smul (n d v : Fin 3 → ℂ) (a : ℂ) :
    parallelCoefficient n d (fun i => a*v i)=a*parallelCoefficient n d v := by
  simp [parallelCoefficient,bilinear,Fin.sum_univ_succ]
  ring

theorem transverse_smul (n d v : Fin 3 → ℂ) (a : ℂ) :
    transverseCoefficient n d (fun i => a*v i)=a*transverseCoefficient n d v := by
  dsimp [transverseCoefficient]
  rw [parallel_smul]
  ring

end
end CentralConfigurations.FiveBody.D2.Regular
