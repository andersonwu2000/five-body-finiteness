import CentralConfigurations.FiveBody.D9RawOrders

namespace CentralConfigurations.FiveBody.D9Raw
open Filter Asymptotics
open scoped Topology
open D9Bridge

variable {mass : Fin 5 → ℂ} {q : ℕ → ZWSystem ℂ 5 mass}

def FarPair (i a : Fin 5) : Prop :=
  (i = 0 ∧ a = 4) ∨ (i = 1 ∧ a = 3) ∨ (i = 2 ∧ a = 3) ∨
  (i = 2 ∧ a = 4) ∨ (i = 3 ∧ a = 4)

variable (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hb : ∀ t, ‖(q t).zVector‖ = ‖(q t).wVector‖)
  (hd : l.diagramCode = akD9Diagram)
include l hb hd

theorem far_z_theta (i a : Fin 5) (h : FarPair i a) : Z q i a =Θ[atTop] eps q := by
  have h03 := (attachment03_single l hb hd).2
  have h14 := (attachment14_single l hb hd).2
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact theta_congr_pointwise
      ((triangle_z_theta l hb hd 0 1 (by decide) (by decide) (by decide)).add_isLittleO h14)
      (fun t => by dsimp [Z]; ring) (fun _ => rfl)
  · exact theta_congr_pointwise
      ((triangle_z_theta l hb hd 1 0 (by decide) (by decide) (by decide)).add_isLittleO h03)
      (fun t => by dsimp [Z]; ring) (fun _ => rfl)
  · exact theta_congr_pointwise
      ((triangle_z_theta l hb hd 2 0 (by decide) (by decide) (by decide)).add_isLittleO h03)
      (fun t => by dsimp [Z]; ring) (fun _ => rfl)
  · exact theta_congr_pointwise
      ((triangle_z_theta l hb hd 2 1 (by decide) (by decide) (by decide)).add_isLittleO h14)
      (fun t => by dsimp [Z]; ring) (fun _ => rfl)
  · exact theta_congr_pointwise
      ((triangle_z_theta l hb hd 0 1 (by decide) (by decide) (by decide)).add_isLittleO (h14.sub h03))
      (fun t => by dsimp [Z]; ring) (fun _ => rfl)

/-- Adding any inner-triangle difference to either long attachment preserves
its order; this is valid even when the attachment is nonmaximal. -/
theorem inner_attachment_w_theta (i b a : Fin 5) (hi : i < 3) (hb' : b < 3)
    (hlong : eps q =o[atTop] W q b a) : W q i a =Θ[atTop] W q b a := by
  have hi := (triangle_w_bigO l hb hd i b hi hb').trans_isLittleO hlong
  exact theta_congr_pointwise (hi.add_isTheta (isTheta_refl (W q b a) atTop))
    (fun t => by dsimp [W]; ring) (fun _ => rfl)

theorem cross_w_long (i a : Fin 5) (hia : D9.Cross i a) :
    eps q =o[atTop] W q i a := by
  have ha : a = 3 ∨ a = 4 := by have := a.isLt; have := hia.2; omega
  rcases ha with rfl | rfl
  · exact (attachment03_single l hb hd).1.trans_isBigO
      (inner_attachment_w_theta l hb hd i 0 3 hia.1 (by decide) (attachment03_single l hb hd).1).2
  · exact (attachment14_single l hb hd).1.trans_isBigO
      (inner_attachment_w_theta l hb hd i 1 4 hia.1 (by decide) (attachment14_single l hb hd).1).2

theorem inner_to_maximal3 (hp : l.w.position 3 ≠ l.w.position 0)
    (i : Fin 5) (hi : i < 3) : W q i 3 =Θ[atTop] scale q := by
  exact (inner_attachment_w_theta l hb hd i 0 3 hi (by decide) (attachment03_single l hb hd).1).trans
    (maximal_w_theta l 0 3 (by decide) hp.symm)

theorem inner_to_maximal4 (hp : l.w.position 4 ≠ l.w.position 1)
    (i : Fin 5) (hi : i < 3) : W q i 4 =Θ[atTop] scale q := by
  exact (inner_attachment_w_theta l hb hd i 1 4 hi (by decide) (attachment14_single l hb hd).1).trans
    (maximal_w_theta l 1 4 (by decide) hp.symm)

theorem skew_outer_w_theta
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (h03 : l.w.position 3 = l.w.position 0) (h14 : l.w.position 4 ≠ l.w.position 1) :
    W q 3 4 =Θ[atTop] scale q := by
  have hsmall := ((triangle_w_bigO l hb hd 0 1 (by decide) (by decide)).trans_isLittleO
    (eps_small_scale ha)).sub (nonmaximal_w_small l 0 3 (by decide) h03.symm)
  exact theta_congr_pointwise (hsmall.add_isTheta (maximal_w_theta l 1 4 (by decide) h14.symm))
    (fun t => by dsimp [W]; ring) (fun _ => rfl)

omit l hb hd

theorem delta_zero_of_far_orders (i j : Fin 5) (hij : i ≠ j)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : Z q i j =Θ[atTop] eps q) (hw : W q i j =Θ[atTop] scale q) :
    Tendsto (fun t => (q t).delta i j) atTop (𝓝 0) := by
  apply D9.zero_of_power (n := 2) (by decide)
  have hh := hz.inv.1.mul hw.inv.1
  have hs : (fun t => (q t).delta i j^2) =O[atTop] eps q := by
    apply hh.congr
    · intro t
      have h := (q t).distance i j hij
      have hZ := (q t).z_separation_ne_zero hij
      have hW := (q t).w_separation_ne_zero hij
      dsimp [Z,W]
      field_simp [hZ,hW]
      linear_combination -h
    · intro t
      rw [← eps_inv_sq]
      field_simp [eps_ne (q := q) t]
  exact hs.trans_tendsto (eps_zero ha)

theorem zForce_small_of_far_orders (i j : Fin 5) (hij : i ≠ j)
    (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
    (hz : Z q i j =Θ[atTop] eps q) (hw : W q i j =Θ[atTop] scale q) :
    (fun t => (q t).zForce i j) =O[atTop] (fun t => eps q t^2) := by
  have hδ := (delta_zero_of_far_orders i j hij ha hz hw).isBigO_one ℂ
  exact (hδ.mul hw.inv.1).congr
    (fun t => by rw [D9.zForce_eq_delta_div_w (q t) i j hij]; rfl)
    (fun t => by simp only [one_mul, ← eps_inv_sq, inv_pow, inv_inv])

theorem zForce_small_of_maximal_attachment
    (l : ScaledZWLimit q (fun t => (q t).inverseScale)) (i j : Fin 5) (hij : i ≠ j)
    (hf : l.w.force i j ≠ 0) (hp : l.w.position i ≠ l.w.position j) :
    (fun t => (q t).zForce i j) =O[atTop] (fun t => eps q t^2) := by
  have hz := maximal_attachment_z_small l i j hij hf hp
  have hδ := maximal_attachment_delta_bounded l i j hij hp
  exact ((hδ.pow 3).mul hz).congr (fun _ => rfl) (fun _ => by simp)

end CentralConfigurations.FiveBody.D9Raw
