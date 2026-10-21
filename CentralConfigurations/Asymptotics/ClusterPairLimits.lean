import CentralConfigurations.Asymptotics.FiniteLimitExtraction
import CentralConfigurations.Asymptotics.SmallSeparationGeometry

/-!
# Pair limits for separated clusters

The inverse-distance variables retain all complex branches. A pair
separated in both leading colors has delta of the normalization scale;
its forces vanish even after division by that scale.
-/

namespace CentralConfigurations
open Filter Asymptotics
open scoped Topology

namespace ScaledZWLimit
variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
  {a : ℕ → ℂ} (l : ScaledZWLimit q a)

theorem delta_cube_limit_of_w_positions_ne
    (hs : ∀ t, a t ≠ 0) (i j : Fin n)
    (hw : l.w.position i ≠ l.w.position j) :
    Tendsto (fun t => (q t).delta i j ^ 3) atTop
      (𝓝 (l.w.force i j / (l.w.position i - l.w.position j))) := by
  have hij : i ≠ j := fun h => hw (congrArg l.w.position h)
  have hW : Tendsto (fun t => a t * ((q t).w i - (q t).w j)) atTop
      (𝓝 (l.w.position i - l.w.position j)) := by
    simpa only [mul_sub] using (l.w_position i).sub (l.w_position j)
  convert (l.w_force i j).div hW (sub_ne_zero.mpr hw) using 1
  funext t
  dsimp [ZWSystem.wForce]
  field_simp [hs t, (q t).w_separation_ne_zero hij]

theorem delta_div_scale_squared_limit
    (hs : ∀ t, a t ≠ 0) (i j : Fin n)
    (hz : l.z.position i ≠ l.z.position j)
    (hw : l.w.position i ≠ l.w.position j) :
    Tendsto (fun t => ((q t).delta i j / a t)^2) atTop
      (𝓝 (((l.z.position i - l.z.position j) *
        (l.w.position i - l.w.position j))⁻¹)) := by
  have hij : i ≠ j := fun h => hz (congrArg l.z.position h)
  have hZ := (l.z_position i).sub (l.z_position j)
  have hW := (l.w_position i).sub (l.w_position j)
  convert (hZ.mul hW).inv₀
    (mul_ne_zero (sub_ne_zero.mpr hz) (sub_ne_zero.mpr hw)) using 1
  funext t
  have he := (q t).distance i j hij
  have hz0 := (q t).z_separation_ne_zero hij
  have hw0 := (q t).w_separation_ne_zero hij
  simp only [← mul_sub]
  field_simp [hs t, hz0, hw0]
  linear_combination he

theorem zForce_div_scale_zero_of_positions_ne
    (hs : ∀ t, a t ≠ 0) (ha : Tendsto a atTop (𝓝 0)) (i j : Fin n)
    (hz : l.z.position i ≠ l.z.position j)
    (hw : l.w.position i ≠ l.w.position j) :
    Tendsto (fun t => (q t).zForce i j / a t) atTop (𝓝 0) := by
  have hd := l.delta_div_scale_squared_limit hs i j hz hw
  have hD : (fun t => (q t).delta i j / a t) =O[atTop] (fun _ => (1 : ℂ)) := by
    apply IsBigO.of_pow (n := 2) (by decide)
    change (fun t => ((q t).delta i j / a t)^2) =O[atTop] (fun _ => (1 : ℂ)^2)
    simpa only [one_pow] using hd.isBigO_one ℂ
  have hZ : (fun t => a t * ((q t).z i - (q t).z j)) =O[atTop]
      (fun _ => (1 : ℂ)) := by
    simpa only [mul_sub] using ((l.z_position i).sub (l.z_position j)).isBigO_one ℂ
  have h := (((hD.pow 3).mul hZ).mul (isBigO_refl a atTop))
  have hf : (fun t => (q t).zForce i j / a t) =O[atTop] a :=
    h.congr (fun t => by dsimp [ZWSystem.zForce]; field_simp [hs t])
      (fun t => by ring)
  exact hf.trans_tendsto ha

end ScaledZWLimit
end CentralConfigurations
