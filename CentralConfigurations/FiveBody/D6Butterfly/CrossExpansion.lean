import CentralConfigurations.FiveBody.D6Butterfly.CrossTaylor
import CentralConfigurations.FiveBody.D6Butterfly.CrossSigns

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology
noncomputable section

theorem torque_product_expansion {f v V W t : ℕ → ℂ} {u L : ℂ}
    (ht : Tendsto t atTop (𝓝 0))
    (hv : v =O[atTop] (fun _ => (1:ℂ))) (hV : V =O[atTop] (fun _ => (1:ℂ)))
    (hW : W =O[atTop] (fun _ => (1:ℂ)))
    (hf : (fun n => f n-u+t n^2*v n) =O[atTop] (fun n => t n^4)) :
    (fun n => t n*f n*(L+t n^2*V n+t n^4*W n)-t n*u*L-
      t n^3*(u*V n-v n*L)) =O[atTop] (fun n => t n^5) := by
  have h2 := (ht.pow 2).isBigO_one ℂ
  have h4 := (ht.pow 4).isBigO_one ℂ
  have hwb := ((isBigO_const_const L (by norm_num : (1:ℂ)≠0) atTop).add (bounded_mul h2 hV)).add (bounded_mul h4 hW)
  have hr : (fun n => t n*(f n-u+t n^2*v n)) =O[atTop] (fun n => t n^5) := by
    simpa only [← pow_succ'] using (isBigO_refl t atTop).mul hf
  have hrest := ((hW.const_mul_left u).sub (bounded_mul hv hV)).sub (bounded_mul h2 (bounded_mul hv hW))
  apply ((order_mul_bounded hr hwb).add (order_mul_bounded (isBigO_refl (fun n => t n^5) atTop) hrest)).congr_left
  intro n
  ring

variable {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q)

def PairGauge.metricLinear (e : Fin 4) : ℂ :=
  (leadingZ (crossLeft e)-leadingZ (crossRight e))*(g.coeff (wCoeff (crossLeft e))-g.coeff (wCoeff (crossRight e)))+
  (leadingW (crossLeft e)-leadingW (crossRight e))*(g.coeff (zCoeff (crossLeft e))-g.coeff (zCoeff (crossRight e)))
def PairGauge.metricQuadratic (e : Fin 4) : ℂ :=
  (g.coeff (zCoeff (crossLeft e))-g.coeff (zCoeff (crossRight e)))*
  (g.coeff (wCoeff (crossLeft e))-g.coeff (wCoeff (crossRight e)))
def PairGauge.wedgeLinear (e : Fin 4) : ℂ :=
  leadingZ (crossRight e)*g.coeff (wCoeff (crossLeft e))+g.coeff (zCoeff (crossRight e))*leadingW (crossLeft e)-
  leadingW (crossRight e)*g.coeff (zCoeff (crossLeft e))-g.coeff (wCoeff (crossRight e))*leadingZ (crossLeft e)
def PairGauge.wedgeQuadratic (e : Fin 4) : ℂ :=
  g.coeff (zCoeff (crossRight e))*g.coeff (wCoeff (crossLeft e))-
  g.coeff (wCoeff (crossRight e))*g.coeff (zCoeff (crossLeft e))

theorem PairGauge.metricError_split (e : Fin 4) :
    g.metricError e=g.time^2*g.metricLinear e+g.time^4*g.metricQuadratic e := by
  rw [g.metricError_eq]
  dsimp [PairGauge.metricLinear,PairGauge.metricQuadratic]
  ring

theorem PairGauge.torqueTerm_chart (e : Fin 4) :
    g.normalized.torqueTerm (crossRight e) (crossLeft e)=g.time*g.crossRoot e^3*
      (-crossSign e+g.time^2*g.wedgeLinear e+g.time^4*g.wedgeQuadratic e) := by
  have hL : leadingZ (crossRight e)*leadingW (crossLeft e)-leadingW (crossRight e)*leadingZ (crossLeft e)= -crossSign e := by
    fin_cases e
    · change (1:ℂ)*1-0*0= -(-1); norm_num
    · change (-1:ℂ)*1-0*0= -1; norm_num
    · change (1:ℂ)*(-1)-0*0= -1; norm_num
    · change (-1:ℂ)*(-1)-0*0= -(-1); norm_num
  change q.delta (crossRight e) (crossLeft e)^3*
    (g.normalized.z (crossRight e)*g.normalized.w (crossLeft e)-
     g.normalized.w (crossRight e)*g.normalized.z (crossLeft e))=_
  rw [q.delta_symm (crossRight e) (crossLeft e),g.z_coordinates,g.z_coordinates,g.w_coordinates,g.w_coordinates]
  dsimp [PairGauge.crossRoot,PairGauge.wedgeLinear,PairGauge.wedgeQuadratic]
  rw [← hL]
  field_simp [g.time_ne]
  ring

variable {m : Fin 5 → ℝ} {qs : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit qs (fun t => (qs t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (gs : ∀ t, PairGauge (qs t))
  (hb : ∀ t, ‖(qs t).zVector‖=‖(qs t).wVector‖)
  (ha : Tendsto (fun t => (qs t).inverseScale) atTop (𝓝 0))
include l hm hd hb ha

theorem cross_coefficient_bounds (e : Fin 4) :
    (fun t => (gs t).metricLinear e) =O[atTop] (fun _ => (1:ℂ)) ∧
    (fun t => (gs t).metricQuadratic e) =O[atTop] (fun _ => (1:ℂ)) ∧
    (fun t => (gs t).wedgeLinear e) =O[atTop] (fun _ => (1:ℂ)) ∧
    (fun t => (gs t).wedgeQuadratic e) =O[atTop] (fun _ => (1:ℂ)) := by
  have C (i : Fin 8) := bigO_one_of_bounded_range (coefficient_bounds l hm hd gs hb ha i)
  refine ⟨?_,?_,?_,?_⟩
  · exact (((C _).sub (C _)).const_mul_left _).add (((C _).sub (C _)).const_mul_left _)
  · exact bounded_mul ((C _).sub (C _)) ((C _).sub (C _))
  · have h := ((((C (wCoeff (crossLeft e))).const_mul_left (leadingZ (crossRight e))).add
        ((C (zCoeff (crossRight e))).const_mul_left (leadingW (crossLeft e)))).sub
        ((C (zCoeff (crossLeft e))).const_mul_left (leadingW (crossRight e))))
        |>.sub ((C (wCoeff (crossRight e))).const_mul_left (leadingZ (crossLeft e)))
    exact h.congr_left (fun t => by dsimp [PairGauge.wedgeLinear]; ring)
  · exact (bounded_mul (C _) (C _)).sub (bounded_mul (C _) (C _))

theorem actual_cross_cube_expansion (e : Fin 4) {u : ℂ}
    (hu : Tendsto (fun t => (gs t).crossRoot e) atTop (𝓝 u)) :
    (fun t => (gs t).crossRoot e^3-u^3+(gs t).time^2*((3/2:ℂ)*u^5*(gs t).metricLinear e)) =O[atTop]
      (fun t => (gs t).time^4) := by
  obtain ⟨hs,hroot⟩ := cross_root_rigidity l hm hd gs hb ha e hu
  have hsn : crossSign e≠0 := by intro hh; have h := cross_sign_sq e; simp [hh] at h
  have hun : u≠0 := by intro hh; simp [hh] at hs; exact hsn hs.symm
  have ht := time_zero l gs (long_separations l hm hd).1 (long_separations l hm hd).2 ha
  have hexp := inverse_cube_second_order hun hsn (by rw [hs,← pow_two]; exact cross_sign_sq e) ht
    (metricError_bigO l hm hd gs hb ha e) hroot (fun t => (gs t).cross_metric e)
  have hG := (cross_coefficient_bounds l hm hd gs hb ha e).2.1
  have h4 := (order_mul_bounded (isBigO_refl (fun t => (gs t).time^4) atTop) hG).const_mul_left ((3/2:ℂ)*u^5)
  apply (hexp.sub h4).congr_left
  intro t
  rw [(gs t).metricError_split]
  dsimp only [PairGauge.crossRoot]
  ring

theorem actual_cross_torque_expansion (e : Fin 4) {u : ℂ}
    (hu : Tendsto (fun t => (gs t).crossRoot e) atTop (𝓝 u)) :
    (fun t => (gs t).normalized.torqueTerm (crossRight e) (crossLeft e)+
      (gs t).time*u^3*crossSign e-(gs t).time^3*(u^3*(gs t).wedgeLinear e+
        (3/2:ℂ)*u^5*(gs t).metricLinear e*crossSign e)) =O[atTop] (fun t => (gs t).time^5) := by
  obtain ⟨hF,-,hV,hW⟩ := cross_coefficient_bounds l hm hd gs hb ha e
  have ht := time_zero l gs (long_separations l hm hd).1 (long_separations l hm hd).2 ha
  have h := torque_product_expansion ht (hF.const_mul_left ((3/2:ℂ)*u^5)) hV hW
    (actual_cross_cube_expansion l hm hd gs hb ha e hu) (L := -crossSign e)
  apply h.congr_left
  intro t
  rw [(gs t).torqueTerm_chart]
  ring

end
end CentralConfigurations.FiveBody.D6
