import CentralConfigurations.FiveBody.D6Butterfly.CrossExpansion

namespace CentralConfigurations.FiveBody.D6
open Filter Asymptotics
open scoped Topology
noncomputable section

def torqueCoefficient (v : Fin 8 → ℂ) (H K : ℂ) : ℂ :=
  (H^3+K^3)*(-v 1+3*(v 6+v 7)/2)+(H^3-K^3)*(-v 0+3*(v 2+v 3)/2)

theorem cross_coefficient_sum {mass : Fin 5 → ℂ} {q : ZWSystem ℂ 5 mass} (g : PairGauge q)
    (h : Fin 4 → ℂ) (hs : ∀ e, h e^2=crossSign e) (h3 : h 3= -h 0) (h1 : h 1= -h 2) :
    (h 0^3*g.wedgeLinear 0+(3/2:ℂ)*h 0^5*g.metricLinear 0*crossSign 0)+
    (h 1^3*g.wedgeLinear 1+(3/2:ℂ)*h 1^5*g.metricLinear 1*crossSign 1)+
    (h 2^3*g.wedgeLinear 2+(3/2:ℂ)*h 2^5*g.metricLinear 2*crossSign 2)+
    (h 3^3*g.wedgeLinear 3+(3/2:ℂ)*h 3^5*g.metricLinear 3*crossSign 3)=
      torqueCoefficient g.coeff (h 0) (h 2) := by
  have h0s : h 0^2= -1 := hs 0
  have h2s : h 2^2=1 := hs 2
  have h05 : h 0^5= -h 0^3 := by rw [show 5=3+2 from rfl,pow_add,h0s]; ring
  have h25 : h 2^5=h 2^3 := by rw [show 5=3+2 from rfl,pow_add,h2s,mul_one]
  rw [h3,h1]
  dsimp [PairGauge.wedgeLinear,PairGauge.metricLinear,crossLeft,crossRight,leadingZ,leadingW,zCoeff,wCoeff,crossSign,torqueCoefficient]
  simp only [show ∀ z : ℂ, (-z)^3= -z^3 by intro z; ring,
    show ∀ z : ℂ, (-z)^5= -z^5 by intro z; ring]
  rw [h05,h25]
  ring

variable {m : Fin 5 → ℝ} {q : ℕ → ZWSystem ℂ 5 (fun i => (m i : ℂ))}
  (l : ScaledZWLimit q (fun t => (q t).inverseScale))
  (hm : ∀ i, 0<m i) (hd : l.diagramCode=fiveBodySourceDiagram 18)
  (g : ∀ t, PairGauge (q t))
  (hb : ∀ t, ‖(q t).zVector‖=‖(q t).wVector‖)
  (ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0))
include l hm hd hb ha

theorem total_cross_torque_expansion {u : Fin 6 → ℂ} {c : Fin 8 → ℂ} {h : Fin 4 → ℂ}
    (hu : ∀ e, Tendsto (fun t => (q t).delta (wingLeft e) (wingRight e)) atTop (𝓝 (u e)))
    (hun : ∀ e, u e≠0) (hc : ∀ i, Tendsto (fun t => (g t).coeff i) atTop (𝓝 (c i)))
    (hh : ∀ e, Tendsto (fun t => (g t).crossRoot e) atTop (𝓝 (h e))) :
    (fun t => fiveBodyCrossTorque (g t).normalized-(m 3:ℂ)*m 0*(g t).time^3*
      torqueCoefficient (g t).coeff (h 0) (h 2)) =O[atTop] (fun t => (g t).time^5) := by
  obtain ⟨h3,h1⟩ := actual_cross_signs l hm hd g hb ha hu hun hc hh
  have hs e := (cross_root_rigidity l hm hd g hb ha e (hh e)).1
  have hE e := actual_cross_torque_expansion l hm hd g hb ha e (hh e)
  obtain ⟨hm01,hm34⟩ := l.five_body_source19_mass_relation hm hb ha hd
  apply ((((hE 0).add (hE 1)).add (hE 2)).add (hE 3) |>.const_mul_left ((m 3:ℂ)*m 0)).congr_left
  intro t
  rw [← cross_coefficient_sum (g t) h hs h3 h1]
  dsimp [fiveBodyCrossTorque,crossLeft,crossRight,crossSign]
  rw [← hm01,← hm34,h3,h1]
  ring

end
end CentralConfigurations.FiveBody.D6
