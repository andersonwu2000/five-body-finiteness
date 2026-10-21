import CentralConfigurations.FiveBody.D9ActualSupport
import CentralConfigurations.FiveBody.D9Exclusion
import CentralConfigurations.Asymptotics.PairEstimates
import CentralConfigurations.Asymptotics.EpsilonOrderScales

namespace CentralConfigurations.FiveBody.D9Raw
open Filter Asymptotics
open scoped Topology BigOperators
open D9Bridge

variable {mass : Fin 5 → ℂ}

abbrev Z (q : ℕ → ZWSystem ℂ 5 mass) (i j : Fin 5) : ℕ → ℂ :=
  fun t => (q t).z i - (q t).z j
abbrev W (q : ℕ → ZWSystem ℂ 5 mass) (i j : Fin 5) : ℕ → ℂ :=
  fun t => (q t).w i - (q t).w j
noncomputable def eps (q : ℕ → ZWSystem ℂ 5 mass) : ℕ → ℂ := fun t => ((q t).epsilon : ℂ)
noncomputable def scale (q : ℕ → ZWSystem ℂ 5 mass) : ℕ → ℂ := fun t => (‖(q t).zVector‖ : ℂ)

variable {q : ℕ → ZWSystem ℂ 5 mass}

theorem eps_ne (t : ℕ) : eps q t ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt ((q t).epsilon_pos 0 1 (by decide)))

theorem eps_sq (t : ℕ) : eps q t ^ 2 = (q t).inverseScale := by
  have h := congrArg Inv.inv ((q t).epsilon_scale)
  simpa only [inv_pow, inv_inv, ZWSystem.inverseScale] using h

theorem eps_inv_sq (t : ℕ) : (eps q t)⁻¹ ^ 2 = scale q t := (q t).epsilon_scale

theorem eps_zero (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    Tendsto (eps q) atTop (𝓝 0) := by
  apply D9.zero_of_power (n := 2) (by decide)
  simpa only [eps_sq] using ha

theorem eps_small_scale (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)) :
    eps q =o[atTop] scale q := by
  simpa only [eps_inv_sq] using epsilon_littleO_inverse_sq (eps q) eps_ne (eps_zero ha)

theorem triangle_w_force_ne (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hd : l.diagramCode = akD9Diagram) (i j : Fin 5)
    (hi : i < 3) (hj : j < 3) (hne : i ≠ j) : l.w.force i j ≠ 0 := by
  have hh : l.w.matrix i j = 1 := by rw [w_matrix l hd, akD9_w_support]; simp [hi,hj]
  simpa [OneColorLimit.matrix, OneColorLimit.Incident, hne] using hh

theorem attachment_z_force_zero (l : ScaledZWLimit q (fun t => (q t).inverseScale))
    (hd : l.diagramCode = akD9Diagram) (i a : Fin 5) (hia : D9.Cross i a) :
    l.z.force i a = 0 := by
  have hne : i ≠ a := by intro h; subst a; have := hia.1; have := hia.2; omega
  have hh : l.z.matrix i a = 0 := by
    rw [z_matrix l hd, akD9_z_support]
    have ha : ¬ a < 3 := by exact not_lt.mpr hia.2
    simp [ha]
  simpa [OneColorLimit.matrix, OneColorLimit.Incident, hne] using hh

variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
  (hd : l.diagramCode = akD9Diagram)
include l hb hd

theorem triangle_z_theta (i j : Fin 5) (hi : i < 3) (hj : j < 3) (hne : i ≠ j) :
    Z q i j =Θ[atTop] eps q := by
  let p := ZWSystem.pairEstimateData q hb i j hne
  have hz := (l.pair_z_stroke_iff hb i j hne).2 (triangle_z_force_ne_zero l hd i j hi hj hne)
  have hw := (l.pair_w_stroke_iff hb i j hne).2 (triangle_w_force_ne l hd i j hi hj hne)
  exact ⟨p.swap.stroke_w_upper hw, p.stroke_z_lower hz⟩

theorem triangle_w_theta (i j : Fin 5) (hi : i < 3) (hj : j < 3) (hne : i ≠ j) :
    W q i j =Θ[atTop] eps q := by
  let p := ZWSystem.pairEstimateData q hb i j hne
  have hz := (l.pair_z_stroke_iff hb i j hne).2 (triangle_z_force_ne_zero l hd i j hi hj hne)
  have hw := (l.pair_w_stroke_iff hb i j hne).2 (triangle_w_force_ne l hd i j hi hj hne)
  exact ⟨p.stroke_w_upper hz, p.swap.stroke_z_lower hw⟩

theorem triangle_z_bigO (i j : Fin 5) (hi : i < 3) (hj : j < 3) :
    Z q i j =O[atTop] eps q := by
  by_cases he : i = j
  · subst j; exact (isBigO_zero (E' := ℂ) (eps q) atTop).congr_left (fun t => by dsimp [Z]; ring)
  · exact (triangle_z_theta l hb hd i j hi hj he).1

theorem triangle_w_bigO (i j : Fin 5) (hi : i < 3) (hj : j < 3) :
    W q i j =O[atTop] eps q := by
  by_cases he : i = j
  · subst j; exact (isBigO_zero (E' := ℂ) (eps q) atTop).congr_left (fun t => by dsimp [W]; ring)
  · exact (triangle_w_theta l hb hd i j hi hj he).1

theorem attachment03_single : eps q =o[atTop] W q 0 3 ∧ Z q 0 3 =o[atTop] eps q := by
  let p := ZWSystem.pairEstimateData q hb 0 3 (by decide)
  exact p.swap.single_z_separations
    ((l.pair_w_stroke_iff hb 0 3 (by decide)).2 (attachment03_w_force_ne_zero l hd))
    ((l.pair_z_absent_iff hb 0 3 (by decide)).2
      (attachment_z_force_zero l hd 0 3 ⟨by decide, by decide⟩))

theorem attachment14_single : eps q =o[atTop] W q 1 4 ∧ Z q 1 4 =o[atTop] eps q := by
  let p := ZWSystem.pairEstimateData q hb 1 4 (by decide)
  exact p.swap.single_z_separations
    ((l.pair_w_stroke_iff hb 1 4 (by decide)).2 (attachment14_w_force_ne_zero l hd))
    ((l.pair_z_absent_iff hb 1 4 (by decide)).2
      (attachment_z_force_zero l hd 1 4 ⟨by decide, by decide⟩))

theorem all_z_differences_small (i j : Fin 5) : Z q i j =O[atTop] eps q := by
  have h0 (i : Fin 5) : Z q i 0 =O[atTop] eps q := by
    fin_cases i
    · exact (isBigO_zero (E' := ℂ) (eps q) atTop).congr_left (fun t => by dsimp [Z]; ring)
    · exact triangle_z_bigO l hb hd 1 0 (by decide) (by decide)
    · exact triangle_z_bigO l hb hd 2 0 (by decide) (by decide)
    · exact (attachment03_single l hb hd).2.isBigO.neg_left.congr_left (fun t => by dsimp [Z]; ring)
    · exact ((triangle_z_bigO l hb hd 1 0 (by decide) (by decide)).sub
        (attachment14_single l hb hd).2.isBigO).congr_left (fun t => by dsimp [Z]; ring)
  exact ((h0 i).sub (h0 j)).congr_left (fun t => by dsimp [Z]; ring)

theorem all_z_positions_small (hM : (∑ i, mass i) ≠ 0) (i : Fin 5) :
    (fun t => (q t).z i) =O[atTop] eps q := by
  have hh : (fun t => ∑ j ∈ Finset.univ.erase i, mass j * Z q i j t) =O[atTop] eps q :=
    IsBigO.sum (fun j _ => (all_z_differences_small l hb hd i j).const_mul_left (mass j))
  apply (isBigO_const_mul_left_iff hM).1
  exact hh.congr_left (fun t => (q t).mass_separation_sum_z i)

omit hb hd

theorem maximal_w_theta (i j : Fin 5) (hne : i ≠ j) (hp : l.w.position i ≠ l.w.position j) :
    W q i j =Θ[atTop] scale q :=
  (l.w_separation_order_iff i j hne i j).2 hp

theorem nonmaximal_w_small (i j : Fin 5) (hne : i ≠ j) (hp : l.w.position i = l.w.position j) :
    W q i j =o[atTop] scale q := (l.w_close_iff i j hne i j).2 hp

theorem maximal_attachment_z_small (i j : Fin 5) (hne : i ≠ j)
    (hf : l.w.force i j ≠ 0) (hp : l.w.position i ≠ l.w.position j) :
    Z q i j =O[atTop] (fun t => eps q t^2) := by
  simpa only [eps_sq] using l.z_separation_bigO_scale_of_maximal_w_pair
    (fun t => by rw [← eps_sq]; exact pow_ne_zero 2 (eps_ne t)) i j hne hf hp

theorem maximal_attachment_delta_bounded (i j : Fin 5) (hne : i ≠ j)
    (hp : l.w.position i ≠ l.w.position j) :
    (fun t => (q t).delta i j) =O[atTop] (fun _ => (1 : ℂ)) := by
  apply IsBigO.of_pow (n := 3) (by decide)
  change (fun t => (q t).delta i j^3) =O[atTop] (fun _ => (1 : ℂ)^3)
  simpa only [one_pow] using (l.delta_cube_limit_of_w_positions_ne
    (fun t => by rw [← eps_sq]; exact pow_ne_zero 2 (eps_ne t)) i j hp).isBigO_one ℂ

end CentralConfigurations.FiveBody.D9Raw



