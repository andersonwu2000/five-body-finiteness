import CentralConfigurations.Asymptotics.SequenceOrders

/-!
# The analytic constraints behind Proposition 4.5

No term of an additive identity can have the unique largest discrete level.
This applies both to three separations and to a separation with its two
endpoint positions. Negation preserves a level, including open levels.
-/

namespace CentralConfigurations

open scoped Topology
open Filter Asymptotics

def OrderTriangle (a b c : Fin 6) : Prop :=
  a ≤ max b c ∧ b ≤ max a c ∧ c ≤ max a b

instance (a b c : Fin 6) : Decidable (OrderTriangle a b c) := inferInstanceAs
  (Decidable (a ≤ max b c ∧ b ≤ max a c ∧ c ≤ max a b))

theorem OrderTriangle.swap_left {a b c : Fin 6} (h : OrderTriangle a b c) :
    OrderTriangle b a c := ⟨h.2.1, h.1, by simpa only [max_comm] using h.2.2⟩

theorem OrderTriangle.rotate {a b c : Fin 6} (h : OrderTriangle a b c) :
    OrderTriangle c a b :=
  ⟨h.2.2, by simpa only [max_comm] using h.1,
    by simpa only [max_comm] using h.2.1⟩

theorem HasOrderLevel.triangle_of_add {s : OrderScales} {f g h : ℕ → ℂ}
    {kf kg kh : Fin 6} (hf : HasOrderLevel s f kf)
    (hg : HasOrderLevel s g kg) (hh : HasOrderLevel s h kh)
    (heq : ∀ t, f t = g t + h t) : OrderTriangle kf kg kh := by
  refine ⟨hf.le_max_of_add hg hh heq, ?_, ?_⟩
  · apply hg.le_max_of_add hf hh.neg
    intro t
    rw [heq t]
    ring
  · apply hh.le_max_of_add hf hg.neg
    intro t
    rw [heq t]
    ring

namespace SequenceOrderAssignment

variable {n : ℕ} {mass : Fin n → ℂ} {q : ℕ → ZWSystem ℂ n mass}
variable {i₀ j₀ : Fin n} {hij₀ : i₀ ≠ j₀}
variable {ha : Tendsto (fun t => (q t).inverseScale) atTop (𝓝 0)}
variable (o : SequenceOrderAssignment q i₀ j₀ hij₀ ha)

theorem z_separation_triangle (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) :
    OrderTriangle (o.z i j) (o.z i k) (o.z k j) :=
  (o.z_separation_level i j hij).triangle_of_add (o.z_separation_level i k hik)
    (o.z_separation_level k j hkj) (fun t => by ring)

theorem w_separation_triangle (i j k : Fin n) (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j) :
    OrderTriangle (o.w i j) (o.w i k) (o.w k j) :=
  (o.w_separation_level i j hij).triangle_of_add (o.w_separation_level i k hik)
    (o.w_separation_level k j hkj) (fun t => by ring)

theorem z_position_triangle (i j : Fin n) (hij : i ≠ j) :
    OrderTriangle (o.z i j) (o.z i i) (o.z j j) :=
  (o.z_separation_level i j hij).triangle_of_add (o.z_position_level i)
    (o.z_position_level j).neg (fun t => by ring)

theorem w_position_triangle (i j : Fin n) (hij : i ≠ j) :
    OrderTriangle (o.w i j) (o.w i i) (o.w j j) :=
  (o.w_separation_level i j hij).triangle_of_add (o.w_position_level i)
    (o.w_position_level j).neg (fun t => by ring)

end SequenceOrderAssignment

end CentralConfigurations
