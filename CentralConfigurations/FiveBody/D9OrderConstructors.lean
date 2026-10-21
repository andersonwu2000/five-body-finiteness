import CentralConfigurations.FiveBody.D9RawGeometry

namespace CentralConfigurations.FiveBody.D9Raw
open Filter Asymptotics
open scoped Topology BigOperators
open D9Bridge

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}
variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
  (hd : l.diagramCode = akD9Diagram)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
  (hM : (∑ i, mass i) ≠ 0)

noncomputable def epsilonLimit : ScaledZWLimit q (fun t => eps q t^2) where
  z := l.z
  w := l.w
  z_position i := by simpa only [eps_sq] using l.z_position i
  w_position i := by simpa only [eps_sq] using l.w_position i
  z_force i j := by simpa only [eps_sq] using l.z_force i j
  w_force i j := by simpa only [eps_sq] using l.w_force i j

include l hb hd ha

theorem both_far_inverse_zero (h03 : l.w.position 3 ≠ l.w.position 0)
    (h14 : l.w.position 4 ≠ l.w.position 1) (i a : Fin 5)
    (h : (i = 0 ∧ a = 4) ∨ (i = 1 ∧ a = 3) ∨
      (i = 2 ∧ a = 3) ∨ (i = 2 ∧ a = 4)) :
    Tendsto (fun t => (q t).delta i a) atTop (𝓝 0) := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact delta_zero_of_far_orders 0 4 (by decide) ha (far_z_theta l hb hd 0 4 (by simp [FarPair]))
      (inner_to_maximal4 l hb hd h14 0 (by decide))
  · exact delta_zero_of_far_orders 1 3 (by decide) ha (far_z_theta l hb hd 1 3 (by simp [FarPair]))
      (inner_to_maximal3 l hb hd h03 1 (by decide))
  · exact delta_zero_of_far_orders 2 3 (by decide) ha (far_z_theta l hb hd 2 3 (by simp [FarPair]))
      (inner_to_maximal3 l hb hd h03 2 (by decide))
  · exact delta_zero_of_far_orders 2 4 (by decide) ha (far_z_theta l hb hd 2 4 (by simp [FarPair]))
      (inner_to_maximal4 l hb hd h14 2 (by decide))

theorem both_exterior_z_small (h03 : l.w.position 3 ≠ l.w.position 0)
    (h14 : l.w.position 4 ≠ l.w.position 1) (i a : Fin 5) (h : D9.Cross i a) :
    (fun t => (q t).zForce i a) =O[atTop] (fun t => eps q t^2) := by
  have hi : i = 0 ∨ i = 1 ∨ i = 2 := by have := h.1; omega
  have ha' : a = 3 ∨ a = 4 := by have := h.2; have := a.isLt; omega
  rcases hi with rfl | rfl | rfl <;> rcases ha' with rfl | rfl
  · exact zForce_small_of_maximal_attachment l 0 3 (by decide)
      (attachment03_w_force_ne_zero l hd) h03.symm
  · exact zForce_small_of_far_orders 0 4 (by decide) ha (far_z_theta l hb hd 0 4 (by simp [FarPair]))
      (inner_to_maximal4 l hb hd h14 0 (by decide))
  · exact zForce_small_of_far_orders 1 3 (by decide) ha (far_z_theta l hb hd 1 3 (by simp [FarPair]))
      (inner_to_maximal3 l hb hd h03 1 (by decide))
  · exact zForce_small_of_maximal_attachment l 1 4 (by decide)
      (attachment14_w_force_ne_zero l hd) h14.symm
  · exact zForce_small_of_far_orders 2 3 (by decide) ha (far_z_theta l hb hd 2 3 (by simp [FarPair]))
      (inner_to_maximal3 l hb hd h03 2 (by decide))
  · exact zForce_small_of_far_orders 2 4 (by decide) ha (far_z_theta l hb hd 2 4 (by simp [FarPair]))
      (inner_to_maximal4 l hb hd h14 2 (by decide))

include hM

/-- Every field is constructed from actual balanced support and maximal
leading attachment separations. No previously derived order list is assumed. -/
noncomputable def bothMaximalOrders (h03 : l.w.position 3 ≠ l.w.position 0)
    (h14 : l.w.position 4 ≠ l.w.position 1) : D9.BothMaximalOrders q where
  eps := eps q
  eps_ne := eps_ne
  eps_zero := eps_zero ha
  limit := epsilonLimit l
  center t := (q t).w 0
  z_small i _ := all_z_positions_small l hb hd hM i
  centered_w_small i hi := triangle_w_bigO l hb hd i 0 hi (by decide)
  exterior_z_small := both_exterior_z_small l hb hd ha h03 h14
  outer_z_separation := far_z_theta l hb hd 3 4 (by simp [FarPair])
  supported_attachment := h03
  sparse3 := outer3_w_force_support l hd
  sparse4 := outer4_w_force_support l hd
  far_inverse_zero := both_far_inverse_zero l hb hd ha h03 h14

/-- The nonmaximal arm keeps its arbitrary actual rate.  The constructor
does not assume any quarter-power orders or fixed intermediate exponent. -/
noncomputable def skewOrders (h03 : l.w.position 3 = l.w.position 0)
    (h14 : l.w.position 4 ≠ l.w.position 1) : D9.SkewOrders q where
  eps := eps q
  eps_zero := eps_zero ha
  center t := (q t).w 0
  z_small i _ := all_z_positions_small l hb hd hM i
  centered_w_small i hi := triangle_w_bigO l hb hd i 0 hi (by decide)
  cross_w_large := cross_w_long l hb hd
  attachment_w_subforce :=
    (nonmaximal_w_small l 0 3 (by decide) h03.symm).trans_isBigO
      ((l.w_stroke_order_iff 0 3 (by decide) 0 3).2 (attachment03_w_force_ne_zero l hd)).2
  other_attachment_bounded := maximal_attachment_delta_bounded l 1 4 (by decide) h14.symm
  opposite_z_small i hi := by
    apply (attachment03_single l hb hd).2.trans_isBigO
    exact (far_z_theta l hb hd i 3 (by rcases hi with rfl | rfl <;> simp [FarPair])).2
  same_w_comparable i hi :=
    (inner_attachment_w_theta l hb hd i 0 3
      (by rcases hi with rfl | rfl <;> decide) (by decide) (attachment03_single l hb hd).1).2
  far_inverse_zero i a h := by
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact delta_zero_of_far_orders 0 4 (by decide) ha (far_z_theta l hb hd 0 4 (by simp [FarPair]))
        (inner_to_maximal4 l hb hd h14 0 (by decide))
    · exact delta_zero_of_far_orders 2 4 (by decide) ha (far_z_theta l hb hd 2 4 (by simp [FarPair]))
        (inner_to_maximal4 l hb hd h14 2 (by decide))
    · exact delta_zero_of_far_orders 3 4 (by decide) ha (far_z_theta l hb hd 3 4 (by simp [FarPair]))
        (skew_outer_w_theta l hb hd ha h03 h14)

end CentralConfigurations.FiveBody.D9Raw
